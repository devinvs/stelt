use std::fs::{read_dir, read_to_string};
use stelt::Lexer;
use stelt::Program;

#[test]
fn test_parser() {
    for entry in read_dir("./tests/parser").unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();

        eprintln!("Testing {:?}", path);

        let should_fail = name.starts_with("bad");

        let mut lexer = Lexer::default();
        let buf = read_to_string(path.clone()).unwrap();

        let mut tokens = lexer.lex(&buf).unwrap();
        let program = Program::parse(&mut tokens);

        if should_fail {
            assert!(program.is_err());
        } else if let Err(e) = program {
            e.pprint(&buf);
            panic!()
        }
    }
}
