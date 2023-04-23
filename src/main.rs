use std::fs::File;
use std::io::Read;

use stelt::Lexer;
use stelt::Program;

fn main() {
    compile("./test.st");
}

fn compile(path: &str) {
    // Read File
    let mut file = File::open(path).unwrap();
    let mut buf = String::with_capacity(file.metadata().unwrap().len() as usize);
    file.read_to_string(&mut buf).unwrap();

    // Lex
    let mut lexer = Lexer::default();
    let mut tokens = lexer.lex(&buf);

    // Parse
    let program = Program::parse(&mut tokens);
    eprintln!("{:#?}", program);

    // Output Code
    //program.compile();
}
