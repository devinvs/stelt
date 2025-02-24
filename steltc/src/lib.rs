mod codegen;
mod error;
mod lexer;
mod lir;
mod llvm;
mod mir;
mod parse_tree;
mod parser;
mod resolve;
mod type_checker;
mod unify;

pub use codegen::Module;
pub use lexer::Lexer;
pub use lexer::Token;
pub use lexer::TokenStream;
pub use mir::gen_impl_map;
pub use mir::MIRTree;
pub use parse_tree::ParseTree as Program;
pub use parse_tree::Type;
pub use type_checker::TypeChecker;

use std::sync::atomic::{AtomicUsize, Ordering};
static ID: AtomicUsize = AtomicUsize::new(0);
fn gen_var(prefix: &str) -> String {
    format!("{prefix}.{}", ID.fetch_add(1, Ordering::SeqCst))
}
