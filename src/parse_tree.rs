use std::collections::HashMap;
use std::collections::LinkedList as List;

use crate::error::Range;

#[derive(Debug)]
pub struct ParseTree {
    pub traits: HashMap<String, Trait>,
    pub impls: Vec<Impl>,
    pub types: HashMap<String, DataDecl>,
    pub typedefs: HashMap<String, Type>,
    pub funcs: HashMap<String, Vec<FunctionDef>>,
    pub defs: HashMap<String, Expression>
}

#[derive(Debug)]
pub struct Trait {
    pub name: String,
    pub var: String,
    pub types: HashMap<String, Type>,
    pub funcs: HashMap<String, Vec<FunctionDef>>,
    pub range: Range,
}

#[derive(Debug)]
pub struct Impl {
    pub trait_name: String,
    pub for_type: Type,
    pub funcs: HashMap<String, Vec<FunctionDef>>,
    pub range: Range,
}

#[derive(Debug)]
/// A data decl is the declaration of either a product type or a sum type.
/// A product type is a list of ident type pairs, a sum type is a list of type
/// constructors. Both have generic type args
pub enum DataDecl {
    Product(String, Vec<String>, Vec<(String, Type)>, Range),
    Sum(String, Vec<String>, Vec<TypeCons>, Range)
}

#[derive(Debug)]
/// A constructor for a single variant of a sum type
pub struct TypeCons {
    pub name: String,
    pub args: Type,
    pub range: Range,
}


#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    ForAll(Vec<String>, Box<Type>, Range),
    Generic(Vec<Type>, Box<Type>, Range),
    Arrow(Box<Type>, Box<Type>, Range),
    Tuple(Vec<Type>, Range),
    List(Box<Type>, Range),
    Ident(String, Range),

    // Builtins
    U8(Range),
    U16(Range),
    U32(Range),
    U64(Range),
    I8(Range),
    I16(Range),
    I32(Range),
    I64(Range),
    Str(Range),
    Unit(Range),

    // Type variable used for parsing. Only present in ir.
    // DOES NOT PARSE
    Var(usize)
}

impl Type {
    pub fn range(&self) -> Range {
        match self {
            Self::ForAll(_, _, r) => r,
            Self::Generic(_, _, r) => r,
            Self::Arrow(_, _, r) => r,
            Self::Tuple(_, r) => r,
            Self::List(_, r) => r,
            Self::Ident(_, r) => r,
            Self::U8(r)
            | Self::U16(r)
            | Self::U32(r)
            | Self::U64(r)
            | Self::I8(r)
            | Self::I16(r)
            | Self::I32(r)
            | Self::I64(r)
            | Self::Str(r)
            | Self::Unit(r) => r,
            _ => panic!()
        }.clone()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub args: Pattern,
    pub body: Expression,
    pub range: Range
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String, Range),

    /// A tuple of expressions
    Tuple(Vec<Expression>, Range),

    /// A list of expressions
    ExprList(Vec<Expression>, Range),

    /// Assign a pattern to an expression
    Let(Pattern, Box<Expression>, Box<Expression>, Range),

    /// If conditional statment
    If(Box<Expression>, Box<Expression>, Box<Expression>, Range),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<Expression>, Vec<(Pattern, Expression)>, Range),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<Expression>, Box<Expression>, Range),

    /// Get the member of a struct
    Member(Box<Expression>, String, Range),

    /// A lambda expression with pattern args and an expression body
    Lambda(Pattern, Box<Expression>, Range),

    // Constant Fields
    Num(u64, Range),    // A Number Literal
    Str(String, Range), // A String Literal
    Unit(Range)
}

impl Expression {
    pub fn range(&self) -> Range {
        match self {
            Expression::Unit(r) => r,
            Expression::Str(_, r) => r,
            Expression::Num(_, r) => r,
            Expression::Lambda(_, _, r) => r,
            Expression::Call(_, _, r) => r,
            Expression::Member(_, _, r) => r,
            Expression::Match(_, _, r) => r,
            Expression::If(_, _, _, r) => r,
            Expression::Let(_, _, _, r) => r,
            Expression::Identifier(_, r) => r,
            Expression::Tuple(_, r) => r,
            Expression::ExprList(_, r) => r,
        }.clone()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern {
    Unit(Range),

    Num(u64, Range),
    Str(String, Range),

    Var(String, Range),

    Tuple(Vec<Pattern>, Range),
    Cons(String, Box<Pattern>, Range)
}

impl Pattern {
    pub fn free_vars(&self) -> List<String> {
        match self {
            Pattern::Var(a, _) => {
                let mut l = List::new();
                l.push_front(a.clone());
                l
            }
            Pattern::Tuple(ps, _) => {
                let mut i = ps.iter();
                let mut l = i.next().unwrap().free_vars();

                for p in i {
                    l.append(&mut p.free_vars());
                }

                l
            }
            Pattern::Cons(_, p, _) => p.free_vars(),
            _ => List::new()
        }
    }

    pub fn range(&self) -> Range {
        *match self {
            Pattern::Var(_, r) => r,
            Pattern::Unit(r) => r,
            Pattern::Num(_, r) => r,
            Pattern::Str(_, r) => r,
            Pattern::Tuple(_, r) => r,
            Pattern::Cons(_, _, r) => r
        }
    }
}
