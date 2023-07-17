use crate::parse_tree::Type;
use lazy_static::lazy_static;
use std::collections::HashMap;

lazy_static! {
    pub static ref BUILTIN: HashMap<String, Type> = {
        let mut m = HashMap::new();

        m.insert("add".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("sub".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("mul".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("div".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("mod".into(), Type::from_str("(i32, i32) -> i32").unwrap());
        m.insert("eq".into(), Type::from_str("(i32, i32) -> Bool").unwrap());

        m
    };
}

pub const BUILTIN_ASM: &str = r#"
define private i32 @add({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = add i32 %a, %b
    ret i32 %res
}

define private i32 @sub({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = sub i32 %a, %b
    ret i32 %res
}

define private i32 @mul({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = mul i32 %a, %b
    ret i32 %res
}

define private i32 @div({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = sdiv i32 %a, %b
    ret i32 %res
}

define private i32 @mod({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = srem i32 %a, %b
    ret i32 %res
}

define private i1 @eq({i32, i32} %in) alwaysinline {
    %a = extractvalue {i32, i32} %in, 0
    %b = extractvalue {i32, i32} %in, 1
    %res = icmp eq i32 %a, %b
    ret i1 %res
}

declare ptr @malloc(i32) nounwind
"#;
