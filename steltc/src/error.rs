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
            .take((pend - pstart) as usize);

        eprintln!("\x1b[1m\x1b[31merror:\x1b[37m {}\x1b[0m", self.msg);
        eprintln!(
            " \x1b[35m-->\x1b[0m {}:{}:{}",
            self.file.to_str().unwrap(),
            self.start.0,
            self.start.1
        );

        for (row, txt) in lines {
            let txt = txt.unwrap();
            let prow = row + 1;

            if row == self.start.0 as usize {
                eprintln!("\x1b[35m{prow:digs$} |\x1b[0m {txt}");
            } else if row == self.end.0 as usize {
                eprintln!("\x1b[35m{prow:digs$} |\x1b[0m {txt}");
            } else {
                eprintln!("\x1b[35m{prow:digs$} |\x1b[0m {txt}");
            }
        }
    }
}
