use std::io::Write;
use termcolor::{StandardStream, Color, ColorChoice, ColorSpec, WriteColor};

#[derive(Debug)]
pub struct SteltError {
    pub range: Option<Range>,
    pub msg: String
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct Range {
    pub l0: usize,
    pub l1: usize,
    pub c0: usize,
    pub c1: usize
}

impl Range {
    pub const fn line(l: usize, start: usize, end: usize) -> Self {
        Range {
            l0: l,
            l1: l,
            c0: start,
            c1: end
        }
    }

    pub fn new(l0: usize, l1: usize, c0: usize, c1: usize) -> Self {
        Self { l0, l1, c0, c1 }
    }

    pub fn add(self, other: Range) -> Range {

        let (l0, c0) = if self.l0 == other.l0 {
            (self.l0, self.c0.min(other.c0))
        } else if self.l0 < other.l0 {
            (self.l0, self.c0)
        } else {
            (other.l0, other.c0)
        };

        let (l1, c1) = if self.l1 == other.l1 {
            (self.l1, self.c1.max(other.c1))
        } else if self.l1 > other.l1 {
            (self.l1, self.c1)
        } else {
            (other.l1, other.c1)
        };

        Range { l0, l1, c0, c1 }
    }
}

impl SteltError {
    pub fn pprint(&self, s: &str) {
        let mut stderr = StandardStream::stderr(ColorChoice::Always);

        let num_lines = s.lines().count();

        let line_nums: Vec<usize> = if let Some(range) = self.range {
            (range.l0.saturating_sub(2)..range.l1+1)
                .filter(|n| *n<num_lines)
                .collect()
        } else {
            (num_lines.saturating_sub(2)..num_lines)
                .filter(|n| *n<num_lines)
                .collect()
        };

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

        if let Some(range) = self.range {
            if n < range.l0 || n > range.l1 {
                stderr.reset().unwrap();
                writeln!(stderr, "{}", l).unwrap();
            } else if n==range.l0 && n==range.l1 {
                stderr.reset().unwrap();
                write!(stderr, "{}", &l[0..range.c0]).unwrap();
                stderr.set_color(ColorSpec::new().set_underline(true).set_fg(Some(Color::Red))).unwrap();
                write!(stderr, "{}", &l[range.c0..range.c1]).unwrap();
                stderr.reset().unwrap();
                writeln!(stderr, "{}", &l[range.c1..]).unwrap();
            } else if n==range.l0 {
                stderr.reset().unwrap();
                write!(stderr, "{}", &l[0..range.c0]).unwrap();
                stderr.set_color(ColorSpec::new().set_underline(true).set_fg(Some(Color::Red))).unwrap();
                writeln!(stderr, "{}", &l[range.c0..]).unwrap();
            } else if n==range.l1 {
                stderr.set_color(ColorSpec::new().set_underline(true).set_fg(Some(Color::Red))).unwrap();
                write!(stderr, "{}", &l[0..range.c1]).unwrap();
                stderr.reset().unwrap();
                writeln!(stderr, "{}", &l[range.c1..]).unwrap();
            } else {
                stderr.reset().unwrap();
                writeln!(stderr, "{}", l).unwrap();
            }
        } else {
            writeln!(stderr, "{}", l).unwrap();
        }
    }

    fn print_err(&self, stderr: &mut StandardStream) {
        stderr.set_color(ColorSpec::new().set_fg(Some(Color::Yellow))).unwrap();

        let arr = if let Some(range) = self.range {
            (range.c1 - range.c0) / 2 + range.c0 + 5
        } else {
            0
        };

        for _ in 0..arr { write!(stderr, " ").unwrap() }
        writeln!(stderr, "^").unwrap();

        let pad = arr.saturating_sub(self.msg.len() * 3 / 4);
        for _ in 0..pad { write!(stderr, " ").unwrap() }

        writeln!(stderr, "{}", self.msg).unwrap();

        stderr.reset().unwrap();
    }
}

