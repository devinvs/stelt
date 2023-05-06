mod error;
mod lexer;
mod parse_tree;
mod parser;
mod mir;
mod unify;
mod type_checker;
//mod codegen;

pub use lexer::Token as Token;
pub use lexer::Lexer as Lexer;
pub use parse_tree::ParseTree as Program;
pub use mir::MIRTree;
pub use type_checker::TypeChecker;

pub use error::SteltError;
