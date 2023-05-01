mod lexer;
mod parse_tree;
mod parser;
//mod typer;
//mod codegen;

pub use lexer::Token as Token;
pub use lexer::Lexer as Lexer;
pub use parse_tree::ParseTree as Program;

#[derive(Debug)]
pub struct SteltError {
    line: usize,
    start: usize,
    end: usize,

    msg: String
}

impl SteltError {
    pub fn pprint(&self, s: &str) {
        eprintln!("{:?}\n", self);
        let line = s.lines().enumerate()
            .filter(|l| l.0==self.line)
            .map(|l| l.1)
            .next()
            .unwrap();

        eprintln!("{line}");
        eprintln!("{}", self.msg);
    }
}
