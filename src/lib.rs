//! An intcode intepreter written in Rust!
//!
//! Intcode is a machine language specified in several challenges from 
//! [Advent of Code 2019](https://adventofcode.com/2019). This library provides a full
//! implementation of the language that is compatible with every Intcode-based challenge.

use std::convert::TryInto;
use std::fmt;

/// An instance of an Intcode virtual machine.
#[derive(Debug)]
pub struct Machine<I, O> {
    mem: Vec<isize>,
    ip: isize,
    base: isize,
    input: I,
    output: O,
}

impl<I, O> Machine<I, O>
where
    I: FnMut() -> isize,
    O: FnMut(isize),
{
    /// Constructs a new machine with the given I/O callbacks and the initial state:
    ///
    /// - empty `mem`;
    /// - `ip` pointing to zero;
    /// - `base` set at zero.
    pub fn new(input: I, output: O) -> Machine<I, O> {
        Machine {
            mem: Vec::new(),
            ip: 0,
            base: 0,
            input,
            output,
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

    fn read(&mut self, i: isize) -> Result<isize, Error> {
        let i: usize = i.try_into()
            .map_err(|_| Error::NegativePointer)?;

        self.reserve(i + 1);
        Ok(self.mem[i])
    }

    fn write(&mut self, i: isize, val: isize) -> Result<(), Error> {
        let i: usize = i.try_into()
            .map_err(|_| Error::NegativePointer)?;

        self.reserve(i + 1);
        self.mem[i] = val;
        Ok(())
    }

    fn param(&mut self, offset: isize) -> Result<isize, Error> {
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
            
            unknown => Err(Error::IllegalMode(unknown)),
        }
    }

    fn out(&mut self, offset: isize, val: isize) -> Result<(), Error> {
        let opcode = self.read(self.ip)?;
        let arg = self.read(self.ip + offset)?;
        let mode = (opcode / 10isize.pow(offset as u32 + 1)) % 10;

        match mode {
            // absolute pointer
            0 => self.write(arg, val),
            
            // relative pointer
            2 => self.write(self.base + arg, val),

            unknown => Err(Error::IllegalMode(unknown)),
        }
    }

    /// Executes a single instruction.
    pub fn step(&mut self) -> Result<(), Error> {
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
                let a = (self.input)();
                self.out(1, a)?;
                self.ip += 2;
                Ok(())
            }

            // out
            4 => {
                let a = self.param(1)?;
                (self.output)(a);
                self.ip += 2;
                Ok(())
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
            99 => Err(Error::Halted),

            unknown => Err(Error::IllegalInstruction(unknown)),
        }
    }

    /// Runs the program until the first error is encountered.
    pub fn run(&mut self) -> Error {
        loop {
            if let Err(e) = self.step() {
                return e;
            }
        }
    }
}

/// Errors that can occur during execution.
#[derive(Debug)]
pub enum Error {
    /// Attempted to use a negative value as a pointer.
    NegativePointer,

    /// Encountered an unknown parameter mode.
    IllegalMode(isize),

    /// Encountered an unknown instruction.
    IllegalInstruction(isize),

    /// Encountered a halt instruction (99).
    Halted,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::NegativePointer => write!(f, "attempted to use a negative value as a pointer"),
            Error::IllegalMode(mode) => write!(f, "illegal mode: {}", mode),
            Error::IllegalInstruction(inst) => write!(f, "illegal instruction: {}", inst),
            Error::Halted => write!(f, "halted"),
        }
    }
}
