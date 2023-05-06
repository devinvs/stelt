use lazy_static::lazy_static;
use std::collections::HashMap;
use crate::parse_tree::Type;

lazy_static! {
    pub static ref BUILTIN: HashMap<String, Type> = {
        let mut m = HashMap::new();

        m.insert("add".into(), Type::from_str("(u64, u64) -> u64").unwrap());

        m
    };
}
