use std::collections::HashMap;
use std::collections::LinkedList as List;
use std::collections::HashSet;

use crate::error::Range;

#[derive(Debug)]
pub struct ParseTree {
    pub types: HashMap<String, DataDecl>,
    pub typedefs: HashMap<String, Type>,
    pub funcs: HashMap<String, Vec<FunctionDef>>,
    pub defs: HashMap<String, Expression>,
    pub external: HashSet<String>
}

#[derive(Debug, Clone)]
/// A data decl is the declaration of either a product type or a sum type.
/// A product type is a list of ident type pairs, a sum type is a list of type
/// constructors. Both have generic type args
pub enum DataDecl {
    Product(String, Vec<String>, Vec<(String, Type)>, Range),
    Sum(String, Vec<String>, Vec<TypeCons>, Range)
}

#[derive(Debug, Clone)]
/// A constructor for a single variant of a sum type
pub struct TypeCons {
    pub name: String,
    pub args: Type,
    pub range: Range,
}


#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    ForAll(Vec<String>, Box<Type>),
    Generic(Vec<Type>, Box<Type>),
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Ident(String),

    // Builtins
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Str,
    Unit,

    // Type variable used for parsing. Only present in ir.
    // DOES NOT PARSE
    Var(usize),
}

impl Type {
    pub fn to_string(&self) -> String {
        match self {
            Type::Generic(args, t) => format!("{}${}$", t.to_string(), args.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(",")),
            Type::Arrow(a, b) => format!("{}->{}", a.to_string(), b.to_string()),
            Type::Tuple(ts) => format!("({})", ts.iter().map(Type::to_string).collect::<Vec<_>>().join(",")),
            Type::Ident(s) => s.clone(),

            Type::U8 => "u8".to_string(),
            Type::U16 => "u16".to_string(),
            Type::U32 => "u32".to_string(),
            Type::U64 => "u64".to_string(),
            Type::I8 => "i8".to_string(),
            Type::I16 => "i16".to_string(),
            Type::I32 => "i32".to_string(),
            Type::I64 => "i64".to_string(),
            Type::Str => "str".to_string(),
            Type::Unit => "()".to_string(),

            _ => panic!()
        }
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
    Unit(Range, Option<Type>),

    Num(u64, Range, Option<Type>),
    Str(String, Range, Option<Type>),

    Var(String, Range, Option<Type>),

    Tuple(Vec<Pattern>, Range, Option<Type>),
    Cons(String, Box<Pattern>, Range, Option<Type>)
}

impl Pattern {
    pub fn free_vars(&self) -> List<String> {
        match self {
            Pattern::Var(a, _, _) => {
                let mut l = List::new();
                l.push_front(a.clone());
                l
            }
            Pattern::Tuple(ps, _, _) => {
                let mut i = ps.iter();
                let mut l = i.next().unwrap().free_vars();

                for p in i {
                    l.append(&mut p.free_vars());
                }

                l
            }
            Pattern::Cons(_, p, _, _) => p.free_vars(),
            _ => List::new()
        }
    }

    pub fn range(&self) -> Range {
        *match self {
            Pattern::Var(_, r, _) => r,
            Pattern::Unit(r, _) => r,
            Pattern::Num(_, r, _) => r,
            Pattern::Str(_, r, _) => r,
            Pattern::Tuple(_, r, _) => r,
            Pattern::Cons(_, _, r, _) => r
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Pattern::Var(_, _, t) => t,
            Pattern::Unit(_, t) => t,
            Pattern::Num(_, _, t) => t,
            Pattern::Str(_, _, t) => t,
            Pattern::Tuple(_, _, t) => t,
            Pattern::Cons(_, _, _, t) => t
        }.clone().unwrap()
    }

    pub fn set_type(&mut self, ty: Type) {
        match self {
            Pattern::Var(_, _, t) => *t = Some(ty),
            Pattern::Unit(_, t) => *t = Some(ty),
            Pattern::Num(_, _, t) => *t = Some(ty),
            Pattern::Str(_, _, t) => *t = Some(ty),
            Pattern::Tuple(_, _, t) => *t = Some(ty),
            Pattern::Cons(_, _, _, t) => *t = Some(ty)
        }
    }
}
