mod lexer;
mod parse_tree;
mod parser;
mod mir;
mod builtin;
mod unify;
mod type_checker;
mod lir;
mod llvm;
mod codegen;

pub use lexer::Token as Token;
pub use lexer::Lexer as Lexer;
pub use parse_tree::ParseTree as Program;
pub use mir::MIRTree;
pub use type_checker::TypeChecker;
pub use codegen::Module;

use std::sync::atomic::{AtomicUsize, Ordering};
static ID: AtomicUsize = AtomicUsize::new(0);
fn gen_var(prefix: &str) -> String {
    format!("{prefix}.{}", ID.fetch_add(1, Ordering::SeqCst))
}

fn id() -> String {
    format!("{}", ID.fetch_add(1, Ordering::SeqCst))
}
