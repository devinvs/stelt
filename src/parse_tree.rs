use std::collections::HashMap;

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
    pub funcs: HashMap<String, Vec<FunctionDef>>
}

#[derive(Debug)]
pub struct Impl {
    pub trait_name: String,
    pub for_type: Type,
    pub funcs: HashMap<String, Vec<FunctionDef>>
}

#[derive(Debug)]
/// The declaration of a new sum type with given name and constructors
pub struct DataDecl {
    pub args: Vec<String>,
    pub cons: Vec<TypeCons>
}

#[derive(Debug)]
/// A constructor for a single variant of a sum type
pub struct TypeCons {
    pub name: String,
    pub args: Vec<Type>
}


#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    ForAll(Vec<String>, Box<Type>),
    Generic(Vec<Type>, Box<Type>),
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
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
    Var(usize)
}

impl Type {
    pub fn name(&self) -> String {
        match self {
            Self::U8 => "u8".into(),
            Self::U16 => "u16".into(),
            Self::U32 => "u32".into(),
            Self::U64 => "u64".into(),
            Self::I8 => "i8".into(),
            Self::I16 => "i16".into(),
            Self::I32 => "i32".into(),
            Self::I64 => "i64".into(),
            Self::Str => "str".into(),
            Self::Ident(s) => s.clone(),
            Self::Unit => "()".into(),
            Self::List(a) => format!("[{}]", a.name()),
            Self::Arrow(a, b) => format!("{}->{}", a.name(), b.name()),
            Self::Generic(a, b) => format!("{}<{}>", b.name(), a.iter().map(|t| t.name()).collect::<Vec<_>>().join(",")),
            Self::Tuple(ts) => format!("({})", ts.iter().map(Type::name).collect::<Vec<_>>().join(",")),
            Self::ForAll(_, b) => b.name(),
            _ => panic!()
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub args: Pattern,
    pub body: Expression
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String),

    /// A tuple of expressions
    Tuple(Vec<Expression>),

    /// A list of expressions
    ExprList(Vec<Expression>),

    /// Assign a pattern to an expression
    Let(Pattern, Box<Expression>, Box<Expression>),

    /// If conditional statment
    If(Box<Expression>, Box<Expression>, Box<Expression>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<Expression>, Vec<(Pattern, Expression)>),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<Expression>, Vec<Expression>),

    /// A lambda expression with pattern args and an expression body
    Lambda(Pattern, Box<Expression>),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal
    EmptyList,
    Unit
}

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern {
    Unit,
    EmptyList,

    Num(u64),
    Str(String),

    Var(String),

    Tuple(Vec<Pattern>),
    Cons(String, Box<Pattern>)
}
