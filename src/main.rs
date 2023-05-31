use std::fs::File;
use std::io::Read;

use stelt::Lexer;
use stelt::Program;
use stelt::MIRTree;
use stelt::TypeChecker;

use stelt::Module;

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
    let mut tokens = match lexer.lex(&buf) {
        Ok(t) => t,
        Err(e) => {
            e.pprint(&buf);
            std::process::exit(1);
        }
    };

    // Parse
    let program = match Program::parse(&mut tokens) {
        Ok(p) => p,
        Err(e) => {
            e.pprint(&buf);
            std::process::exit(1);
        }
    };

    let mut mir = MIRTree::from(program);

    let mut checker = TypeChecker::default();
    match checker.check_program(&mut mir) {
        Ok(_) => {}
        Err(e) => {
            e.pprint(&buf);
            std::process::exit(1);
        }
    }
    let lir = mir.lower();
    eprintln!("{:#?}", lir.funcs);

    let out = File::create("./out.ll").unwrap();
    let mut module = Module::new(Box::new(out));
    module.compile(lir).unwrap();
}
