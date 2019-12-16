//! An intcode intepreter written in Rust!
//!
//! Intcode is a machine language specified in several challenges from 
//! [Advent of Code 2019](https://adventofcode.com/2019). This library provides a full
//! implementation of the language that is compatible with every Intcode-based challenge.

use std::convert::TryInto;
use std::fmt;

/// An instance of an Intcode virtual machine.
#[derive(Debug)]
pub struct Machine {
    mem: Vec<isize>,
    ip: isize,
    base: isize,
}

impl Machine {
    /// Constructs a new machine with the initial state:
    ///
    /// - empty `mem`;
    /// - `ip` pointing to zero;
    /// - `base` set at zero.
    pub fn new() -> Machine {
        Machine {
            mem: Vec::new(),
            ip: 0,
            base: 0,
        }
    }

    /// An immutable view into the virtual machine's memory.
    pub fn mem(&self) -> &[isize] {
        &self.mem
    }

    /// A mutable view into the virtual machine's memory.
    pub fn mem_mut(&mut self) -> &mut [isize] {
        &mut self.mem
    }

    /// Ensures that memory locations `0..size` are valid, extending memory with zeroes if needed.
    pub fn reserve(&mut self, size: usize) {
        if self.mem.len() < size {
            self.mem.resize(size, 0);
        }
    }

    /// Copies the given slice into memory at the given location.
    pub fn copy(&mut self, start: usize, values: &[isize]) {
        self.reserve(start + values.len());
        self.mem[start..start+values.len()].copy_from_slice(values);
    }

    fn read(&mut self, i: isize) -> Result<isize, Exit> {
        let i: usize = i.try_into()
            .map_err(|_| Exit::NegativePointer)?;

        self.reserve(i + 1);
        Ok(self.mem[i])
    }

    fn write(&mut self, i: isize, val: isize) -> Result<(), Exit> {
        let i: usize = i.try_into()
            .map_err(|_| Exit::NegativePointer)?;

        self.reserve(i + 1);
        self.mem[i] = val;
        Ok(())
    }

    fn param(&mut self, offset: isize) -> Result<isize, Exit> {
        let opcode = self.read(self.ip)?;
        let arg = self.read(self.ip + offset)?;
        let mode = (opcode / 10isize.pow(offset as u32 + 1)) % 10;
        
        match mode {
            // absolute pointer
            0 => self.read(arg),

            // immediate
            1 => Ok(arg),

            // relative pointer
            2 => self.read(self.base + arg),
            
            unknown => Err(Exit::IllegalMode(unknown)),
        }
    }

    fn out(&mut self, offset: isize, val: isize) -> Result<(), Exit> {
        let opcode = self.read(self.ip)?;
        let arg = self.read(self.ip + offset)?;
        let mode = (opcode / 10isize.pow(offset as u32 + 1)) % 10;

        match mode {
            // absolute pointer
            0 => self.write(arg, val),
            
            // relative pointer
            2 => self.write(self.base + arg, val),

            unknown => Err(Exit::IllegalMode(unknown)),
        }
    }

    /// Executes a single instruction.
    pub fn step(&mut self, input: Option<isize>) -> Result<(), Exit> {
        let opcode = self.read(self.ip)?;
        let instruction = opcode % 100;

        match instruction {
            // add
            1 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                self.out(3, a + b)?;
                self.ip += 4;
                Ok(())
            }

            // mul
            2 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                self.out(3, a * b)?;
                self.ip += 4;
                Ok(())
            }

            // in
            3 => {
                let a = input.ok_or(Exit::Input)?;
                self.out(1, a)?;
                self.ip += 2;
                Ok(())
            }

            // out
            4 => {
                let a = self.param(1)?;
                self.ip += 2;
                Err(Exit::Output(a))
            }

            // jt
            5 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                if a != 0 {
                    self.ip = b;
                } else {
                    self.ip += 3;
                }
                Ok(())
            }

            // jf
            6 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                if a == 0 {
                    self.ip = b;
                } else {
                    self.ip += 3;
                }
                Ok(())
            }

            // lt
            7 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                self.out(3, if a < b { 1 } else { 0 })?;
                self.ip += 4;
                Ok(())
            }

            // eq
            8 => {
                let a = self.param(1)?;
                let b = self.param(2)?;
                self.out(3, if a == b { 1 } else { 0 })?;
                self.ip += 4;
                Ok(())
            }

            // arb
            9 => {
                let a = self.param(1)?;
                self.base += a;
                self.ip += 2;
                Ok(())
            }

            // halt
            99 => Err(Exit::Halted),

            unknown => Err(Exit::IllegalInstruction(unknown)),
        }
    }

    /// Runs the program until the first error is encountered.
    pub fn run(&mut self, mut input: Option<isize>) -> Exit {
        loop {
            match self.step(input.take()) {
                Ok(_) => {}
                Err(e) => return e,
            }
        }
    }
}

/// Errors that can occur during execution.
#[derive(Debug)]
pub enum Exit {
    /// Attempted to use a negative value as a pointer.
    NegativePointer,

    /// Encountered an unknown parameter mode.
    IllegalMode(isize),

    /// Encountered an unknown instruction.
    IllegalInstruction(isize),

    /// The program encountered an `in` instruction and needs to take input.
    Input,
    
    /// The program encountered an `out` instruction and needs to return output.
    Output(isize),

    /// Encountered a halt instruction (99).
    Halted,
}

impl fmt::Display for Exit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Exit::NegativePointer => write!(f, "attempted to use a negative value as a pointer"),
            Exit::IllegalMode(mode) => write!(f, "illegal mode: {}", mode),
            Exit::IllegalInstruction(inst) => write!(f, "illegal instruction: {}", inst),
            Exit::Input => write!(f, "need input"),
            Exit::Output(a) => write!(f, "got output: {}", a),
            Exit::Halted => write!(f, "halted"),
        }
    }
}
