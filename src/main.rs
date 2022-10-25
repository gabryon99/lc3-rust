use core::time;
use std::{
    fs::File,
    io::{BufReader, Read, Write},
    path::PathBuf,
};

use clap::Parser;

use byteorder::{BigEndian, ReadBytesExt};
use termios::tcsetattr;

#[derive(Debug, Parser)]
struct Args {
    #[clap(short, long)]
    binary_filename: PathBuf,
    #[clap(default_value_t = 0, short)]
    emulation_speed: u64,
    #[clap(short, long)]
    pretty_print: bool,
}

mod mem {
    pub const MEMORY_MAX: usize = 1 << 16;
    // Space left for trap routines
    pub const PC_START: u16 = 0x3000;

    pub enum MemoryMappedRegister {
        KBSR = 0xFE00, // Keyboard status
        KBDR = 0xFE02, // Keyboard data
    }
}

mod reg {
    pub const R_R0: usize = 0;
    pub const R_R1: usize = 1;
    pub const R_R2: usize = 2;
    pub const R_R3: usize = 3;
    pub const R_R4: usize = 4;
    pub const R_R5: usize = 5;
    pub const R_R6: usize = 6;
    pub const R_R7: usize = 7;
    pub const R_PC: usize = 8;
    pub const R_COND: usize = 9;
    pub const R_COUNT: usize = 10;
}

mod cpu {

    pub enum Flag {
        POS = 1 << 0,
        ZRO = 1 << 1,
        NEG = 1 << 2,
    }

    #[derive(Debug, Clone, Copy)]
    pub enum OpCode {
        BR = 0, // Branch
        ADD,    // Add
        LD,     //Load
        ST,     // Store
        JSR,    // Jump Register
        AND,    // Bitwise and
        LDR,    // Load register
        STR,    // Store register
        RTI,    // unused
        NOT,    //Bitwise not
        LDI,    // Load indirect
        STI,    // Store indirect
        JMP,    // Jump
        RES,    // Reserved (unused)
        LEA,    // Load effective address
        TRAP,   // Execute Trap
        UKN,    // Unknown
    }

    #[derive(Debug)]
    pub enum TrapCode {
        UKN = 0x00,   // Unknown, raise error
        GETC = 0x20,  // Get a character from keyboard, not echoed onto the terminal
        OUT = 0x21,   // Output a character
        PUTS = 0x22,  // Output a word string
        IN = 0x23,    // Get character from keyboard, echoed onto the terminal
        PUTSP = 0x24, // Output a byte program
        HALT = 0x25,  // Halt the program
    }

    impl OpCode {
        pub fn from_u16(op: u16) -> Self {
            match op {
                0x00 => Self::BR,
                0x01 => Self::ADD,
                0x02 => Self::LD,
                0x03 => Self::ST,
                0x04 => Self::JSR,
                0x05 => Self::AND,
                0x06 => Self::LDR,
                0x07 => Self::STR,
                0x08 => Self::RTI,
                0x09 => Self::NOT,
                0x0a => Self::LDI,
                0x0b => Self::STI,
                0x0c => Self::JMP,
                0x0d => Self::RES,
                0x0e => Self::LEA,
                0x0f => Self::TRAP,
                _ => Self::UKN,
            }
        }
    }

    impl TrapCode {
        pub fn from_u16(code: u16) -> Self {
            match code {
                0x20 => Self::GETC,
                0x21 => Self::OUT,
                0x22 => Self::PUTS,
                0x23 => Self::IN,
                0x24 => Self::PUTSP,
                0x25 => Self::HALT,
                _ => Self::UKN,
            }
        }
    }
}

#[derive(Debug)]
struct LC3 {
    memory: [u16; mem::MEMORY_MAX],
    regs: [u16; reg::R_COUNT],
    running: bool,
}

fn get_char() -> u8 {
    let mut buff = [0; 1];
    std::io::stdin().read_exact(&mut buff).unwrap();
    buff[0]
}

impl LC3 {
    fn new() -> Self {
        let mut vm = Self {
            memory: [0; mem::MEMORY_MAX],
            regs: [0; reg::R_COUNT],
            running: true,
        };

        // Set the Z flag
        vm.regs[reg::R_COND] = cpu::Flag::ZRO as u16;
        // The PC starts at address 0x3000
        vm.regs[reg::R_PC] = mem::PC_START;

        vm
    }

    fn mem_read(&mut self, address: usize) -> u16 {
        use mem::MemoryMappedRegister::{KBDR, KBSR};

        if address == (KBSR as usize) {
            let mut buffer = [0; 1];
            std::io::stdin()
                .read_exact(&mut buffer)
                .expect("Error during char reading");
            if buffer[0] != 0 {
                self.mem_write(KBSR as usize, 1 << 15);
                self.mem_write(KBDR as usize, buffer[0] as u16);
            } else {
                self.mem_write(KBSR as usize, 0)
            }
        }

        self.memory[address]
    }

    fn mem_write(&mut self, address: usize, val: u16) {
        self.memory[address] = val;
    }

    fn update_flags(&mut self, r: u16) {
        if self.regs[r as usize] == 0 {
            self.regs[reg::R_COND] = cpu::Flag::ZRO as u16;
        } else if (self.regs[r as usize] >> 15) == 1 {
            self.regs[reg::R_COND] = cpu::Flag::NEG as u16;
        } else {
            self.regs[reg::R_COND] = cpu::Flag::POS as u16;
        }
    }

    fn sign_extend(mut x: u16, bit_count: i32) -> u16 {
        if ((x >> (bit_count - 1)) & 1) != 0 {
            x |= 0xFFFF << bit_count;
        }
        x
    }

    fn add(&mut self, instr: u16) {
        // Destination Operand
        let r0 = (instr >> 9) & 0x7;
        // First operand
        let r1 = (instr >> 6) & 0x7;
        // Whether we are in immediate mode
        let imm_flag = (instr >> 5) & 0x1;

        if imm_flag == 1 {
            let imm5 = LC3::sign_extend(instr & 0x1F, 5);
            let val = imm5 as u32 + self.regs[r1 as usize] as u32;
            self.regs[r0 as usize] = val as u16;
        } else {
            let r2 = instr & 0x7;
            let val = self.regs[r1 as usize] as u32 + self.regs[r2 as usize] as u32;
            self.regs[r0 as usize] = val as u16;
        }

        self.update_flags(r0);
    }

    fn and(&mut self, instr: u16) {
        let r0 = (instr >> 9) & 0x7;
        let r1 = (instr >> 6) & 0x7;
        let imm_flag = (instr >> 5) & 0x1;

        if imm_flag == 1 {
            let imm5 = LC3::sign_extend(instr & 0x1F, 5);
            self.regs[r0 as usize] = self.regs[r1 as usize] & imm5;
        } else {
            let r2 = instr & 0x7;
            self.regs[r0 as usize] = self.regs[r1 as usize] & self.regs[r2 as usize];
        }

        self.update_flags(r0);
    }

    fn not(&mut self, instr: u16) {
        let r0 = (instr >> 9) & 0x7;
        let r1 = (instr >> 6) & 0x7;
        self.regs[r0 as usize] = !self.regs[r1 as usize];
        self.update_flags(r0);
    }

    fn br(&mut self, instr: u16) {
        let pc_offset = LC3::sign_extend(instr & 0x1FF, 9);
        let cond_flag = (instr >> 9) & 0x7;
        if (cond_flag & self.regs[reg::R_COND]) > 0 {
            let sum = self.regs[reg::R_PC] as usize + pc_offset as usize;
            self.regs[reg::R_PC] = sum as u16;
        }
    }

    fn ldi(&mut self, instr: u16) {
        let r0 = (instr >> 9) & 0x7;
        let pc_offset = LC3::sign_extend(instr & 0x1FFF, 9);

        let t = self.mem_read((self.regs[reg::R_PC] + pc_offset) as usize);
        let address = self.mem_read(t as usize);

        self.regs[r0 as usize] = address;

        self.update_flags(r0)
    }

    fn jmp(&mut self, instr: u16) {
        let dest = (instr >> 6) & 0x7;
        self.regs[reg::R_PC] = self.regs[dest as usize];
    }

    fn jsr(&mut self, instr: u16) {
        let long_flag = (instr >> 11) & 0x1;
        self.regs[reg::R_R7] = self.regs[reg::R_PC];
        if long_flag == 0 {
            let base_r = (instr >> 6) & 0x7;
            self.regs[reg::R_PC] = base_r; // JSRR
        } else {
            let offset = LC3::sign_extend(instr & 0x7ff, 11);
            self.regs[reg::R_PC] += offset;
        }
    }

    fn ld(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let offset = LC3::sign_extend(instr & 0x1ff, 9);
        self.regs[dr as usize] = self.mem_read((self.regs[reg::R_PC] + offset) as usize);
        self.update_flags(dr);
    }

    fn ldr(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let base_r = (instr >> 6) & 0x7;
        let offset = LC3::sign_extend(instr & 0x3F, 6);

        let loc = self.regs[base_r as usize] as usize + offset as usize;
        let val = self.mem_read(loc).clone();

        self.regs[dr as usize] = val;
        self.update_flags(dr);
    }

    fn lea(&mut self, instr: u16) {
        let r0 = (instr >> 9) & 0x7;
        let offset = LC3::sign_extend(instr & 0x1FF, 9);
        self.regs[r0 as usize] = self.regs[reg::R_PC] + offset;
        self.update_flags(r0);
    }

    fn st(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x07;
        let offset = LC3::sign_extend(instr & 0x1ff, 9);
        let address = self.regs[reg::R_PC] as usize + offset as usize;
        let address = address as u16;
        self.mem_write(address as usize, self.regs[sr as usize]);
    }

    fn sti(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x07;
        let offset = LC3::sign_extend(instr & 0x1ff, 9);
        let address = self.mem_read((self.regs[reg::R_PC] + offset) as usize);
        self.mem_write(address as usize, sr);
    }

    fn str(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let base_r = (instr >> 6) & 0x7;
        let offset = LC3::sign_extend(instr & 0x3f, 6);

        let address = (self.regs[base_r as usize] as usize) + offset as usize;
        let address = address as u16;

        self.mem_write(address as usize, self.regs[dr as usize]);
    }

    fn trap(&mut self, instr: u16) {
        let trapvect8 = instr & 0xff;
        self.regs[reg::R_R7] = self.regs[reg::R_PC];

        /*
        eprintln!(
            "[Debug] :: Trap instruction: {:?}",
            cpu::TrapCode::from_u16(trapvect8)
            ); */

        match cpu::TrapCode::from_u16(trapvect8) {
            cpu::TrapCode::UKN => panic!("Unknown trap code!"),
            cpu::TrapCode::GETC => {
                self.regs[reg::R_R0] = get_char() as u16;
            }
            cpu::TrapCode::OUT => {
                let ch = self.regs[reg::R_R0] as u8;
                print!("{}", ch as char);
            }
            cpu::TrapCode::PUTS => {
                let mut i = self.regs[reg::R_R0] as usize;
                let mut c = self.mem_read(i);
                while c != 0 {
                    print!("{}", (c as u8) as char);
                    i += 1;
                    c = self.mem_read(i);
                }
                std::io::stdout().flush().expect("Failed to flush");
            }
            cpu::TrapCode::IN => {
                print!("Enter a character: ");
                std::io::stdout().flush().expect("Failed to flush.");
                let ch = std::io::stdin()
                    .bytes()
                    .next()
                    .and_then(|r| r.ok())
                    .map(|b| b as u16)
                    .unwrap();
                self.regs[reg::R_R0] = ch;

                self.update_flags(reg::R_R0 as u16);
            }
            cpu::TrapCode::PUTSP => {
                let mut i = self.regs[reg::R_R0] as usize;
                let mut c = self.mem_read(i);
                while c != 0 {
                    let char1 = c & 0xff;
                    print!("{}", (char1 as u8) as char);

                    let char2 = c >> 8;
                    if char2 != 0 {
                        print!("{}", (char2 as u8) as char);
                    }

                    i += 1;
                    c = self.mem_read(i);
                }
                std::io::stdout().flush().expect("Failed to flush.");
            }
            cpu::TrapCode::HALT => {
                eprintln!("HALT");
                self.running = false;
            }
        }
    }

    fn read_image_from_file(&mut self, path: PathBuf) {
        let file = File::open(path).expect("File not found!");

        let mut reader = BufReader::new(file);

        let base_address = reader.read_u16::<BigEndian>().expect("Error");
        let mut address = base_address as usize;

        loop {
            match reader.read_u16::<BigEndian>() {
                Ok(instr) => {
                    self.mem_write(address, instr);
                    address += 1;
                }
                Err(e) => {
                    if e.kind() == std::io::ErrorKind::UnexpectedEof {
                        println!("OK")
                    } else {
                        eprintln!("Failed: {}", e);
                    }
                    break;
                }
            }
        }
    }

    fn prettyprint_program(path: PathBuf) {
        let file = File::open(path).expect("File not found!");
        let mut reader = BufReader::new(file);
        let mut line = 0;

        loop {
            match reader.read_u16::<BigEndian>() {
                Ok(instr) => {
                    let opcode = instr >> 12;
                    println!("{}: {:?}", line, cpu::OpCode::from_u16(opcode));
                    line += 1;
                }
                Err(e) => {
                    if e.kind() == std::io::ErrorKind::UnexpectedEof {
                        eprintln!("OK")
                    } else {
                        eprintln!("Failed: {}", e);
                    }
                    break;
                }
            }
        }
    }

    fn dump_memory_from_pc(&self, offset: i32) {
        print!("[Debug] :: [{:#06x}]: ", self.regs[reg::R_PC]);
        let start = self.regs[reg::R_PC] as usize;
        for byte in &self.memory[start..(start + (offset as usize))] {
            print!("{:#06x} ", byte);
        }
        println!("")
    }

    fn dump_memory(&self) {
        let lines = self.memory.len() / 16;
        let mut i = 0;
        for _ in 0..lines {
            eprint!("[{:#06x}]: ", i);
            let j = i;
            for b in &self.memory[j..(j + 16)] {
                eprint!("{:#06} ", b);
                i += 1;
            }
            eprint!(" | ");
            for b in &self.memory[j..(j + 16)] {
                let ch = (*b as u8) as char;
                if ch.is_whitespace() || ch == '\0' {
                    eprint!(".");
                } else {
                    eprint!("{}", ch);
                }
            }
            eprintln!(" |");
        }
    }

    fn dump_registers(&self) {
        eprintln!(
            "[Debug] :: PC={:#x}, COND={:#x}, R0={:#x}, R1={:#x}, R2={:#x}, R3={:#x}, R4={:#x}, R5={:#x}, R6={:#x}, R7={:#x}",
            self.regs[reg::R_PC],
            self.regs[reg::R_COND],
            self.regs[reg::R_R0],
            self.regs[reg::R_R1],
            self.regs[reg::R_R2],
            self.regs[reg::R_R3],
            self.regs[reg::R_R4],
            self.regs[reg::R_R5],
            self.regs[reg::R_R6],
            self.regs[reg::R_R7],
        );
    }

    fn dump(&mut self, op: cpu::OpCode, instr: u16) {
        eprintln!("[Debug] :: OpCode: {:?}, Instr: {:#06x}", op, instr);
        self.dump_registers();
        self.dump_memory_from_pc(16);
        eprintln!();
    }

    fn start(&mut self, speed: u64) {
        #[cfg(debug_assertions)]
        {
            eprintln!("[Debug] :: Running VM, emulation speed: {} ms", speed);
            self.dump_memory();
        }

        loop {
            let instr = self.mem_read(self.regs[reg::R_PC] as usize);
            self.regs[reg::R_PC] += 1;

            let op = cpu::OpCode::from_u16(instr >> 12);

            #[cfg(debug_assertions)]
            self.dump(op.clone(), instr);

            if speed > 0 {
                std::thread::sleep(time::Duration::from_millis(speed));
            }

            match op {
                cpu::OpCode::BR => self.br(instr),
                cpu::OpCode::ADD => self.add(instr),
                cpu::OpCode::LD => self.ld(instr),
                cpu::OpCode::ST => self.st(instr),
                cpu::OpCode::JSR => self.jsr(instr),
                cpu::OpCode::AND => self.and(instr),
                cpu::OpCode::LDR => self.ldr(instr),
                cpu::OpCode::STR => self.str(instr),
                cpu::OpCode::NOT => self.not(instr),
                cpu::OpCode::LDI => self.ldi(instr),
                cpu::OpCode::STI => self.sti(instr),
                cpu::OpCode::JMP => self.jmp(instr),
                cpu::OpCode::LEA => self.lea(instr),
                cpu::OpCode::TRAP => self.trap(instr),
                cpu::OpCode::RTI => panic!("Aborting due to RTI..."),
                cpu::OpCode::RES => panic!("Aborting due to RES..."),
                cpu::OpCode::UKN => {
                    panic!("Unknown OpCode inside memory!")
                }
            }

            if !self.running {
                break;
            }
        }
    }
}

fn main() {
    let stdin = 0;
    let termios = termios::Termios::from_fd(stdin).unwrap();

    // make a mutable copy of termios
    // that we will modify
    let mut new_termios = termios.clone();
    new_termios.c_iflag &= termios::IGNBRK
        | termios::BRKINT
        | termios::PARMRK
        | termios::ISTRIP
        | termios::INLCR
        | termios::IGNCR
        | termios::ICRNL
        | termios::IXON;
    new_termios.c_lflag &= !(termios::ICANON | termios::ECHO); // no echo and canonical mode

    tcsetattr(stdin, termios::TCSANOW, &mut new_termios).unwrap();

    let args = Args::parse();
    if args.pretty_print {
        LC3::prettyprint_program(args.binary_filename);
        return;
    }

    // Create a new VM instance.
    let mut vm = LC3::new();
    vm.read_image_from_file(args.binary_filename);
    vm.start(args.emulation_speed);

    tcsetattr(stdin, termios::TCSANOW, &termios).unwrap();
}
