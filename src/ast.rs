use std::collections::HashMap;

#[derive(Debug)]
pub struct ProgramTree {
    pub traits: HashMap<String, Trait>,
    pub impls: HashMap<String, Vec<(String, Type)>>,
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


#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    ForAll(Vec<String>, Box<Type>),
    Generic(Vec<Type>, Box<Type>),
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Ident(String),
    Unit,

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
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub args: Pattern,
    pub body: Vec<Expression>
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String),

    /// A tuple of expressions
    Tuple(Vec<Expression>),

    /// A list of expressions
    List(Vec<Expression>),

    /// Assign a pattern to an expression
    Let(Pattern, Box<Expression>),
    
    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<Expression>, Vec<(Pattern, Expression)>),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<Expression>, Vec<Expression>),

    /// A lambda expression with pattern args and an expression body
    Lambda(Vec<Pattern>, Box<Expression>),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal
    EmptyList
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
