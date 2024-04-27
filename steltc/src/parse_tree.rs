use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::LinkedList as List;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Vis {
    Public,
    Private,
    Import,
}

#[derive(Debug, Clone)]
pub struct ParseTree {
    pub types: HashMap<String, (Vis, DataDecl)>,

    pub external: HashSet<String>,
    pub typedecls: HashMap<String, (Vis, QualType)>,

    pub typefuns: HashMap<String, (Vis, TypeFun)>,
    pub impls: Vec<Impl>,

    pub funcs: HashMap<String, Vec<FunctionDef>>,
    pub defs: HashMap<String, Expression>,

    pub type_aliases: HashMap<String, Type>,
    pub aliases: HashMap<String, String>,

    pub private_impl_map: HashMap<String, Vec<(String, Type)>>,

    pub imports: HashSet<String>,
    pub import_idents: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct TypeFun {
    pub name: String,
    pub vars: Vec<String>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Impl {
    pub fn_name: String,
    pub gen_args: Vec<String>,
    pub args: Vec<QualType>,
    pub body: Vec<FunctionDef>,
}

#[derive(Debug, Clone)]
/// A data decl is the declaration of either a product type or a sum type.
/// A product type is a list of ident type pairs, a sum type is a list of type
/// constructors. Both have generic type args
pub struct DataDecl(pub String, pub Vec<String>, pub Vec<TypeCons>);

impl DataDecl {
    pub fn remove_recursion(self, name: &str, data: &mut Vec<(String, (Vis, DataDecl))>) -> Self {
        let DataDecl(tname, args, cons) = self;
        DataDecl(
            tname,
            args,
            cons.into_iter()
                .map(|cons| TypeCons {
                    name: cons.name,
                    args: cons.args.remove_recursion(name, data),
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone)]
/// A constructor for a single variant of a sum type
pub struct TypeCons {
    pub name: String,
    pub args: Type,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Constraint(pub String, pub Vec<Type>);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct QualType(pub Vec<Constraint>, pub Type);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    ForAll(Vec<String>, Vec<crate::mir::Constraint>, Box<Type>),
    Generic(Vec<Type>, Box<Type>),
    Arrow(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),

    Ident(String),
    GenVar(String),

    // Builtins
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Bool,
    Unit,
    Str,

    // Type variable used for parsing. Only present in ir.
    // DOES NOT PARSE
    Var(usize),
    NumVar(usize),
    Box(Box<Type>), // funny
}

impl Type {
    fn remove_recursion(self, name: &str, data: &mut Vec<(String, (Vis, DataDecl))>) -> Self {
        match self {
            Type::Ident(i) => {
                if name == i {
                    Type::Box(Box::new(Type::Ident(i)))
                } else if let Some(d) = data
                    .iter_mut()
                    .find(|(a, _)| *a == i)
                    .map(|(_, (_, a))| a.clone())
                {
                    *data
                        .iter_mut()
                        .find(|(a, _)| *a == i)
                        .map(|(_, (_, a))| a)
                        .unwrap() = d.clone().remove_recursion(name, data);
                    Type::Ident(i)
                } else {
                    Type::Ident(i)
                }
            }
            Type::Generic(args, t) => {
                if Type::Generic(args.clone(), t.clone()).to_string() == name {
                    Type::Box(Box::new(Type::Generic(args, t)))
                } else {
                    Type::Generic(args, Box::new(t.remove_recursion(name, data)))
                }
            }
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(a.remove_recursion(name, data)),
                Box::new(b.remove_recursion(name, data)),
            ),
            Type::Tuple(ts) => Type::Tuple(
                ts.into_iter()
                    .map(|t| t.remove_recursion(name, data))
                    .collect(),
            ),
            Type::ForAll(vars, cons, t) => {
                if vars.contains(&name.to_string()) {
                    Type::ForAll(vars, cons, t)
                } else {
                    Type::ForAll(vars, cons, Box::new(t.remove_recursion(name, data)))
                }
            }
            a => a,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Type::Generic(args, t) => format!(
                "{}${}$",
                t.to_string(),
                args.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join("_")
            ),
            Type::Arrow(a, b) => format!("{}--{}", a.to_string(), b.to_string()),
            Type::Tuple(ts) => format!(
                "tup${}$",
                ts.iter().map(Type::to_string).collect::<Vec<_>>().join("_")
            ),
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
            a => panic!("{:?}", a),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub args: Pattern,
    pub body: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String),

    /// A list of expressions
    List(Vec<Expression>),

    /// A tuple of expressions
    Tuple(Vec<Expression>),

    /// Assign a pattern to an expression
    Let(Pattern, Box<Expression>, Box<Expression>),

    /// If conditional statment
    If(Box<Expression>, Box<Expression>, Box<Expression>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<Expression>, Vec<(Pattern, Expression)>),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<Expression>, Box<Expression>),

    /// A lambda expression with pattern args and an expression body
    Lambda(Pattern, Box<Expression>),

    // Constant Fields
    Num(u64), // A Number Literal
    Unit,
    True,
    False,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Pattern {
    Unit(Option<Type>),

    Num(i64, Option<Type>),
    True,
    False,

    Var(String, Option<Type>),

    Tuple(Vec<Pattern>, Option<Type>),
    Cons(String, Box<Pattern>, Option<Type>),

    Any(Option<Type>),
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
            _ => List::new(),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Pattern::True | Pattern::False => &Some(Type::Bool),
            Pattern::Any(t) => t,
            Pattern::Var(_, t) => t,
            Pattern::Unit(t) => t,
            Pattern::Num(_, t) => t,
            Pattern::Tuple(_, t) => t,
            Pattern::Cons(_, _, t) => t,
        }
        .clone()
        .unwrap()
    }

    pub fn set_type(&mut self, ty: Type) {
        match self {
            Pattern::True | Pattern::False => {}
            Pattern::Any(t) => *t = Some(ty),
            Pattern::Var(_, t) => *t = Some(ty),
            Pattern::Unit(t) => *t = Some(ty),
            Pattern::Num(_, t) => *t = Some(ty),
            Pattern::Tuple(_, t) => *t = Some(ty),
            Pattern::Cons(_, _, t) => *t = Some(ty),
        }
    }
}
