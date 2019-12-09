use std::io::{stdin, BufRead};

use intcodeint::Machine;

fn main() {
    let stdin = stdin();
    let handle = stdin.lock();
    let mut lines = handle.lines()
        .map(|result| result.expect("input/output error"));

    if let Some(code) = lines.next() {
        let nums: Vec<isize> = code.split(",")
            .map(|s| s.parse().expect("invalid code"))
            .collect();

        let mut machine = Machine::new(
            // input
            lines.map(|s| s.parse().expect("invalid input")),

            //output
            |int| println!("{}", int),
        );
        machine.copy(0, &nums);
        let result = machine.run();
        eprintln!("terminated: {}", result);
    }
}
