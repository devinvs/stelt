use std::fs::{read_dir, read_to_string};
use stelt::Lexer;

#[test]
fn test_lexer() {
    for entry in read_dir("./tests/lexer").unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();

        eprintln!("Testing {:?}", path);

        let should_fail = name.starts_with("bad");

        let mut lexer = Lexer::default();
        let buf = read_to_string(path.clone()).unwrap();

        let out = lexer.lex(&buf);

        if should_fail {
            assert!(out.is_err());
        } else if let Err(e) = out {
            e.pprint(&buf);
            panic!("{:?} passed but should have failed", name)
        }
    }
}
