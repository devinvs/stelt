use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::path::PathBuf;

pub struct SrcError<'a> {
    file: &'a PathBuf,
    start: (u32, u32),
    end: (u32, u32),
    msg: String,
}

impl<'a> SrcError<'a> {
    pub fn new(file: &'a PathBuf, start: (u32, u32), end: (u32, u32), msg: String) -> Self {
        SrcError {
            file,
            start,
            end,
            msg,
        }
    }

    pub fn print(&self) {
        let r = BufReader::new(File::open(&self.file).unwrap());

        // pstart and pend are where we start and stop printing the file,
        // not the start of the actual highlighted section
        let pstart = self.start.0.saturating_sub(1);
        let pend = self.end.0.saturating_add(1);

        // calculate the number of digist to print for each line no
        let digs = (pstart + 1).ilog10().max((pend + 1).ilog10()) as usize;

        let lines = r
            .lines()
            .enumerate()
            .skip(pstart as usize)
            .take((pend - pstart + 1) as usize);

        eprintln!(
            " \x1b[35m-->\x1b[0m {}:{}:{}",
            self.file.to_str().unwrap(),
            self.start.0 + 1,
            self.start.1 + 1
        );

        let mut init = false;

        for (row, txt) in lines {
            let txt = txt.unwrap();

            let prow = if row as u32 <= self.end.0 && row as u32 >= self.start.0 {
                format!("{:digs$}", row + 1)
            } else {
                let digs = digs + 1;
                format!("{:digs$}", "")
            };

            if row == self.start.0 as usize {
                let (start, end) = txt.split_at(self.start.1 as usize);
                eprint!("\x1b[35m{prow} |\x1b[0m {start}");

                if self.start.0 == self.end.0 {
                    let (start, end) = end.split_at((self.end.1 - self.start.1 + 1) as usize);
                    eprintln!("\x1b[4m\x1b[31m{start}\x1b[0m{end}\x1b[0m");
                } else {
                    eprintln!("\x1b[4m\x1b[31m{end}\x1b[0m");
                    init = true;
                }
            } else if row == self.end.0 as usize {
                let (start, end) = txt.split_at(self.end.1 as usize + 1);
                eprintln!("\x1b[35m{prow} |\x1b[0m \x1b[4m\x1b[31m{start}\x1b[0m{end}");
                init = false;
            } else {
                if init {
                    eprintln!("\x1b[35m{prow} |\x1b[0m \x1b[4m\x1b[31m{txt}\x1b[0m");
                } else {
                    eprintln!("\x1b[35m{prow} |\x1b[0m {txt}");
                }
            }
        }
        eprintln!("\x1b[1m\x1b[31merror:\x1b[37m {}\x1b[0m", self.msg);
        eprintln!("");
    }
}
