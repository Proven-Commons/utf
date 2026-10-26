// UTF-16 in Rust, for tests/cross_check.py. Reads one line per input of
// UTF-16 code units, four hex digits each, and prints "OK:" and the
// code points String::from_utf16 reads, in lower case hex separated by
// commas, or "REJECT". With the argument "lossy", prints "OK:" and the
// code points of String::from_utf16_lossy.
use std::io::{self, BufRead, BufWriter, Write};

fn main() {
    let stdin = io::stdin();
    let mut out = BufWriter::new(io::stdout());
    let lossy = std::env::args().nth(1).as_deref() == Some("lossy");
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let units: Vec<u16> = (0..line.len() / 4)
            .map(|i| u16::from_str_radix(&line[4 * i..4 * i + 4], 16).unwrap())
            .collect();
        let text = if lossy {
            Some(String::from_utf16_lossy(&units))
        } else {
            String::from_utf16(&units).ok()
        };
        match text {
            Some(s) => {
                let parts: Vec<String> = s.chars().map(|c| format!("{:x}", c as u32)).collect();
                writeln!(out, "OK:{}", parts.join(",")).unwrap();
            }
            None => writeln!(out, "REJECT").unwrap(),
        }
    }
}
