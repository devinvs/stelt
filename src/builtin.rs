use lazy_static::lazy_static;
use std::collections::HashMap;
use crate::parse_tree::Type;

lazy_static! {
    pub static ref BUILTIN: HashMap<String, Type> = {
        let mut m = HashMap::new();

        m.insert("add".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("sub".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("mul".into(), Type::from_str("(i32, i32) -> i32").unwrap());

        m
    };
}

pub const BUILTIN_ASM: &'static str = r#"
define i32 @add({i32, i32} %arg.0) alwaysinline {
    %arg1 = extractvalue {i32, i32} %arg.0, 0
    %arg2 = extractvalue {i32, i32} %arg.0, 1
    %res = add i32 %arg1, %arg2
    ret i32 %res
}

define i32 @sub({i32, i32} %arg.0) alwaysinline {
    %arg1 = extractvalue {i32, i32} %arg.0, 0
    %arg2 = extractvalue {i32, i32} %arg.0, 1
    %res = sub i32 %arg1, %arg2
    ret i32 %res
}

define i32 @mul({i32, i32} %arg.0) alwaysinline {
    %arg1 = extractvalue {i32, i32} %arg.0, 0
    %arg2 = extractvalue {i32, i32} %arg.0, 1
    %res = mul i32 %arg1, %arg2
    ret i32 %res
}

define i1 @eq({i32, i32} %arg.0) alwaysinline {
    %arg1 = extractvalue {i32, i32} %arg.0, 0
    %arg2 = extractvalue {i32, i32} %arg.0, 1
    %res = icmp eq i32 %arg1, %arg2
    ret i1 %res
}
"#;
