use std::io::{stdin, BufRead};

use intcodeint::{Machine, Exit};

fn main() {
    let stdin = stdin();
    let handle = stdin.lock();
    let mut lines = handle.lines()
        .map(|result| result.expect("input/output error"));

    if let Some(code) = lines.next() {
        let nums: Vec<isize> = code.split(",")
            .map(|s| s.parse().expect("invalid code"))
            .collect();

        let mut machine = Machine::new();
        machine.copy(0, &nums);
        let mut input = None;
        loop {
            let exit = machine.run(input.take());
            match exit {
                Exit::Input => {
                    if let Some(line) = lines.next() {
                        input = Some(line.parse().expect("invalid input"));
                    } else {
                        eprintln!("terminated: {}", exit);
                        break;
                    }
                }
                Exit::Output(a) => {
                    println!("{}", a);
                }
                _ => {
                    eprintln!("terminated: {}", exit);
                    break;
                }
            }
        }
    }
}
