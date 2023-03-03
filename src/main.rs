use std::fs::File;
use std::io::Read;

use stelt::Lexer;
use stelt::parser::Program;

fn main() {
    let path = "./test.st";

    let mut f = File::open(path).unwrap();
    let mut s = String::new();

    f.read_to_string(&mut s).unwrap();

    let mut lexer = Lexer::default();
    let mut tokens = lexer.lex(&s);
    println!("{:?}", tokens);

    let tree = Program::parse(&mut tokens);
    println!("{:#?}", tree);
}
