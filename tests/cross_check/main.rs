// Reads one hex-encoded byte string per line and prints whether Rust's
// std::str::from_utf8 accepts it, with the code points it reads: "OK:"
// and lower case hex code points separated by commas, or "REJECT".
// Used by tests/cross_check.py.
use std::io::{self, BufRead, BufWriter, Write};

fn main() {
    let stdin = io::stdin();
    let mut out = BufWriter::new(io::stdout());
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let bytes: Option<Vec<u8>> = (0..line.len() / 2)
            .map(|i| u8::from_str_radix(&line[2 * i..2 * i + 2], 16).ok())
            .collect();
        match bytes.and_then(|b| String::from_utf8(b).ok()) {
            Some(s) => {
                let parts: Vec<String> = s.chars().map(|c| format!("{:x}", c as u32)).collect();
                writeln!(out, "OK:{}", parts.join(",")).unwrap();
            }
            None => writeln!(out, "REJECT").unwrap(),
        }
    }
}
