use std::fs::{read_dir, read_to_string};
use stelt::Lexer;
use stelt::Program;
use stelt::MIRTree;
use stelt::TypeChecker;

#[test]
fn test_type_checker() {
    for entry in read_dir("./tests/type_checker").unwrap() {
        let path = entry.unwrap().path();

        eprintln!("Testing {:?}", path);

        let should_fail = path.starts_with("bad");

        let mut lexer = Lexer::default();
        let buf = read_to_string(path.clone()).unwrap();

        let mut tokens = lexer.lex(&buf).unwrap();
        let program = Program::parse(&mut tokens).unwrap();

        let mir = MIRTree::from(program);

        let mut checker = TypeChecker::default();
        let out = checker.check_program(&mir);

        if should_fail {
            assert!(out.is_err());
        } else if let Err(e) = out {
            e.pprint(&buf);
            panic!()
        }
    }
}
