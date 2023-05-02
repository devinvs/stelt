use std::io::Write;
use termcolor::{StandardStream, Color, ColorChoice, ColorSpec, WriteColor};

#[derive(Debug)]
pub struct SteltError {
    pub line: usize,
    pub start: usize,
    pub end: usize,

    pub msg: String
}

impl SteltError {
    pub fn pprint(&self, s: &str) {
        let mut stderr = StandardStream::stderr(ColorChoice::Always);

        let num_lines = s.lines().count();
        let line_nums: Vec<usize> = match self.line {
            0 if self.start==0 && self.end==0 => vec![num_lines-1],
            0 => vec![0],
            1 => vec![0, 1],
            n => vec![n-2, n-1, n]
        }.into_iter().filter(|n| *n<num_lines).collect();

        let mut lines = s.lines().skip(line_nums[0]);

        self.print_empty(&mut stderr);
        for n in line_nums {
            self.print_line(&mut stderr, n, lines.next().unwrap())
        }

        self.print_err(&mut stderr);
    }

    fn print_empty(&self, stderr: &mut StandardStream) {
        stderr.set_color(ColorSpec::new()
                         .set_fg(Some(Color::Blue))
                         .set_bold(true)).unwrap();
        writeln!(stderr, "  | ").unwrap();
        stderr.reset().unwrap();
    }

    fn print_line(&self, stderr: &mut StandardStream, n: usize, l: &str) {
        stderr.set_color(ColorSpec::new().set_fg(Some(Color::Blue)).set_bold(true)).unwrap();
        write!(stderr, "{} | ", n+1).unwrap();
        stderr.reset().unwrap();

        if self.line == n && (self.start != 0 && self.end != 0) {
            write!(stderr, "{}", &l[0..self.start]).unwrap();

            stderr.set_color(ColorSpec::new().set_underline(true).set_fg(Some(Color::Red))).unwrap();
            write!(stderr, "{}", &l[self.start..self.end]).unwrap();
            stderr.reset().unwrap();

            writeln!(stderr, "{}", &l[self.end..]).unwrap();
        } else {
            writeln!(stderr, "{}", l).unwrap();
        }
    }

    fn print_err(&self, stderr: &mut StandardStream) {
        stderr.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();

        let arr =if self.start == 0 && self.end == 0 {
            0
        } else {
            (self.end - self.start) / 2 + self.start + 4
        };

        for _ in 0..arr { write!(stderr, " ").unwrap() }
        writeln!(stderr, "^").unwrap();

        let pad = arr.saturating_sub(self.msg.len() * 3 / 4);
        for _ in 0..pad { write!(stderr, " ").unwrap() }

        writeln!(stderr, "{}", self.msg).unwrap();

        stderr.reset().unwrap();
    }
}

