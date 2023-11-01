use std::fs::{read_dir, read_to_string};
use stelt::Lexer;
use stelt::MIRTree;
use stelt::Program;
use stelt::TypeChecker;

#[test]
fn test_type_checker() {
    for entry in read_dir("./tests/type_checker").unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();

        eprintln!("Testing {:?}", path);

        let should_fail = name.starts_with("bad");

        let mut lexer = Lexer::default();
        let buf = read_to_string(path.clone()).unwrap();

        let mut tokens = lexer.lex(&buf).unwrap();
        let program = Program::parse(&mut tokens).unwrap();

        let mut mir = MIRTree::from(program);

        let mut checker = TypeChecker::default();
        let out = checker.check_program(&mut mir);

        if should_fail {
            assert!(out.is_err());
        } else if let Err(e) = out {
            eprintln!("{e}");
            panic!()
        }
    }
}
