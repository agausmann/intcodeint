//! An intcode intepreter written in Rust!
//!
//! Intcode is a machine language specified in several challenges from
//! [Advent of Code 2019](https://adventofcode.com/2019). This library provides a full
//! implementation of the language that is compatible with every Intcode-based challenge.

use std::convert::TryInto;
use std::fmt;
use std::thread::{self, JoinHandle};

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

    pub fn with_program(program: &[isize]) -> Machine {
        let mut machine = Machine::new();
        machine.copy(0, program);
        machine
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
        self.mem[start..start + values.len()].copy_from_slice(values);
    }

    fn read(&mut self, i: isize) -> Result<isize, Exit> {
        let i: usize = i.try_into().map_err(|_| Exit::NegativePointer)?;

        self.reserve(i + 1);
        Ok(self.mem[i])
    }

    fn write(&mut self, i: isize, val: isize) -> Result<(), Exit> {
        let i: usize = i.try_into().map_err(|_| Exit::NegativePointer)?;

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
    pub fn resume(&mut self, mut input: Option<isize>) -> Exit {
        loop {
            match self.step(input.take()) {
                Ok(_) => {}
                Err(e) => return e,
            }
        }
    }

    /// Runs the program using the given I/O interfaces.
    pub fn run<I, O>(&mut self, input: I, output: O) -> Exit
    where
        I: IntoIterator<Item = isize>,
        O: FnMut(isize),
    {
        let mut input = input.into_iter().peekable();
        let mut output = output;
        let mut next_input = None;
        loop {
            match self.resume(next_input.take()) {
                Exit::Input if input.peek().is_some() => {
                    next_input = input.next();
                }
                Exit::Output(a) => {
                    output(a);
                }
                other => return other,
            }
        }
    }

    pub fn spawn<I, O>(mut self, input: I, output: O) -> JoinHandle<(Machine, Exit)>
    where
        I: IntoIterator<Item = isize> + Send + 'static,
        O: FnMut(isize) + Send + 'static,
    {
        thread::spawn(move || {
            let result = self.run(input, output);
            (self, result)
        })
    }
}

/// Errors that can occur during execution.
#[derive(Debug, PartialEq)]
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

#[cfg(test)]
mod tests {
    use super::*;

    fn run(program: &[isize], input: &[isize]) -> (Machine, Exit, Vec<isize>) {
        let mut machine = Machine::with_program(program);
        let mut output = Vec::new();

        let exit = machine.run(input.iter().copied(), |a| output.push(a));
        (machine, exit, output)
    }

    #[test]
    fn day2a() {
        let (machine, exit, _output) = run(&[1, 9, 10, 3, 2, 3, 11, 0, 99, 30, 40, 50], &[]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(machine.mem()[0], 3500);
    }

    #[test]
    fn day5a_io() {
        let (_machine, exit, output) = run(&[3, 0, 4, 0, 99], &[95243]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[95243]);
    }

    #[test]
    fn day5a_mode() {
        let (_machine, exit, _output) = run(&[1002, 4, 3, 4, 33], &[]);
        assert_eq!(exit, Exit::Halted);
    }

    const DAY5B_CMP: &[isize] = &[
        3, 21, 1008, 21, 8, 20, 1005, 20, 22, 107, 8, 21, 20, 1006, 20, 31, 1106, 0, 36, 98, 0, 0,
        1002, 21, 125, 20, 4, 20, 1105, 1, 46, 104, 999, 1105, 1, 46, 1101, 1000, 1, 20, 4, 20,
        1105, 1, 46, 98, 99,
    ];

    #[test]
    fn day5b_cmp_lt() {
        let (_machine, exit, output) = run(DAY5B_CMP, &[5]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[999]);
    }

    #[test]
    fn day5b_cmp_gt() {
        let (_machine, exit, output) = run(DAY5B_CMP, &[9]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[1001]);
    }

    #[test]
    fn day5b_cmp_eq() {
        let (_machine, exit, output) = run(DAY5B_CMP, &[8]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[1000]);
    }

    fn day7a(program: &[isize]) -> isize {
        let mut result = isize::min_value();
        for a in 0..5 {
            let a_out = run(program, &[a, 0]).2[0];

            for b in 0..5 {
                if b == a {
                    continue;
                }
                let b_out = run(program, &[b, a_out]).2[0];

                for c in 0..5 {
                    if c == a || c == b {
                        continue;
                    }
                    let c_out = run(program, &[c, b_out]).2[0];

                    for d in 0..5 {
                        if d == a || d == b || d == c {
                            continue;
                        }
                        let d_out = run(program, &[d, c_out]).2[0];

                        for e in 0..5 {
                            if e == a || e == b || e == c || e == d {
                                continue;
                            }
                            let e_out = run(program, &[e, d_out]).2[0];

                            result = result.max(e_out);
                        }
                    }
                }
            }
        }

        result
    }

    #[test]
    fn day7a_1() {
        const DAY7A_1: &[isize] = &[
            3, 15, 3, 16, 1002, 16, 10, 16, 1, 16, 15, 15, 4, 15, 99, 0, 0,
        ];

        assert_eq!(day7a(DAY7A_1), 43210);
    }

    #[test]
    fn day7a_2() {
        const DAY7A_2: &[isize] = &[
            3, 23, 3, 24, 1002, 24, 10, 24, 1002, 23, -1, 23, 101, 5, 23, 23, 1, 24, 23, 23, 4, 23, 99,
            0, 0,
        ];

        assert_eq!(day7a(DAY7A_2), 54321);
    }

    #[test]
    fn day7a_3() {
        const DAY7A_3: &[isize] = &[
            3, 31, 3, 32, 1002, 32, 10, 32, 1001, 31, -2, 31, 1007, 31, 0, 33, 1002, 33, 7, 33, 1, 33,
            31, 31, 1, 32, 31, 31, 4, 31, 99, 0, 0, 0,
        ];

        assert_eq!(day7a(DAY7A_3), 65210);
    }

    fn day7b(program: &[isize]) -> isize {
        use std::sync::mpsc;

        let mut result = isize::min_value();

        for a in 5..10 {
            for b in 5..10 {
                if b == a {
                    continue;
                }
                for c in 5..10 {
                    if c == a || c == b {
                        continue;
                    }
                    for d in 5..10 {
                        if d == a || d == b || d == c {
                            continue;
                        }
                        for e in 5..10 {
                            if e == a || e == b || e == c || e == d {
                                continue;
                            }

                            let (main_tx, a_rx) = mpsc::channel();
                            let (a_tx, b_rx) = mpsc::channel();
                            let (b_tx, c_rx) = mpsc::channel();
                            let (c_tx, d_rx) = mpsc::channel();
                            let (d_tx, e_rx) = mpsc::channel();
                            let (e_tx, main_rx) = mpsc::channel();

                            main_tx.send(a).unwrap();
                            a_tx.send(b).unwrap();
                            b_tx.send(c).unwrap();
                            c_tx.send(d).unwrap();
                            d_tx.send(e).unwrap();
                            main_tx.send(0).unwrap();

                            Machine::with_program(program)
                                .spawn(a_rx, move |x| a_tx.send(x).unwrap());
                            Machine::with_program(program)
                                .spawn(b_rx, move |x| b_tx.send(x).unwrap());
                            Machine::with_program(program)
                                .spawn(c_rx, move |x| c_tx.send(x).unwrap());
                            Machine::with_program(program)
                                .spawn(d_rx, move |x| d_tx.send(x).unwrap());
                            Machine::with_program(program)
                                .spawn(e_rx, move |x| e_tx.send(x).unwrap());

                            let mut last = 0;
                            for x in main_rx {
                                last = x;
                                let _ = main_tx.send(x);
                            }
                            result = result.max(last);
                        }
                    }
                }
            }
        }

        result
    }

    #[test]
    fn day7b_1() {
        const DAY7B_1: &[isize] = &[
            3, 26, 1001, 26, -4, 26, 3, 27, 1002, 27, 2, 27, 1, 27, 26, 27, 4, 27, 1001, 28, -1, 28,
            1005, 28, 6, 99, 0, 0, 5,
        ];

        assert_eq!(day7b(DAY7B_1), 139629729);
    }

    #[test]
    fn day7b_2() {
        const DAY7B_2: &[isize] = &[
            3, 52, 1001, 52, -5, 52, 3, 53, 1, 52, 56, 54, 1007, 54, 5, 55, 1005, 55, 26, 1001, 54, -5,
            54, 1105, 1, 12, 1, 53, 54, 53, 1008, 54, 0, 55, 1001, 55, 1, 55, 2, 53, 55, 53, 4, 53,
            1001, 56, -1, 56, 1005, 56, 6, 99, 0, 0, 0, 0, 10,
        ];

        assert_eq!(day7b(DAY7B_2), 18216);
    }

    #[test]
    fn day9_quine() {
        const PROGRAM: &[isize] = &[109,1,204,-1,1001,100,1,100,1008,100,16,101,1006,101,0,99];

        let (_machine, exit, output) = run(PROGRAM, &[]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, PROGRAM);
    }

    #[test]
    fn day9_overflow_check() {
        let (_machine, exit, output) = run(&[1102,34915192,34915192,7,4,7,99,0], &[]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[1219070632396864]);
    }

    #[test]
    fn day9_read_check() {
        let (_machine, exit, output) = run(&[104,1125899906842624,99], &[]);
        assert_eq!(exit, Exit::Halted);
        assert_eq!(output, &[1125899906842624]);
    }
}
