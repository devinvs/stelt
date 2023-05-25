use std::collections::HashMap;
use std::collections::HashSet;

use crate::parse_tree::{
    ParseTree,
    Expression,
    Type,
    DataDecl,
    Pattern
};

use crate::error::Range;
use crate::unify::apply_unifier;
use crate::unify::Term;

type Theta = HashMap<Term<String>, Term<String>>;

#[derive(Debug)]
pub struct MIRTree {
    pub external: HashSet<String>,
    pub types: HashMap<String, DataDecl>,
    pub typedefs: HashMap<String, Type>,
    pub structs: HashMap<String, HashMap<String, Type>>,
    pub funcs: HashMap<String, MIRExpression>,
    pub defs: HashMap<String, MIRExpression>,

    pub constructors: HashMap<String, Type>,
    pub declarations: HashMap<String, Type>,
}

impl MIRTree {
    pub fn from(tree: ParseTree) -> Self {
        // Add all user defined type definitions to declaratiosn
        let mut declarations = HashMap::new();

        for (name, t) in tree.typedefs.iter() {
            declarations.insert(name.clone(), t.clone());
        }

        // Add all type constructors to conss
        let mut constructors = HashMap::new();
        let mut structs = HashMap::new();

        for (name, decl) in tree.types.iter() {
            match decl {
                DataDecl::Sum(_, args, cons, _) => {
                    for cons in cons {
                        let outt = if args.len() == 0 {
                            Box::new(Type::Ident(name.clone()))
                        } else {
                            Box::new(Type::Generic(
                                args.clone().into_iter().map(|s| Type::Ident(s)).collect(),
                                Box::new(Type::Ident(name.clone())), 
                            ))
                        };

                        constructors.insert(
                            format!("{name}.{}", cons.name),
                            Type::ForAll(
                                args.clone(),
                                Box::new(Type::Arrow(
                                    Box::new(cons.args.clone()),
                                    outt,
                                    )
                                ),
                            )
                        );
                    }
                }
                DataDecl::Product(_, args, members, _) => {
                    // Add an entry into the structs map
                    let mut m = HashMap::new();
                    members.iter().for_each(|(n, t)| {m.insert(n.clone(), t.clone());});

                    structs.insert(name.clone(), m);

                    // add constructor
                    let outt = if args.len() == 0 {
                        Box::new(Type::Ident(name.clone()))
                    } else {
                        Box::new(Type::Generic(
                            args.clone().into_iter().map(|s| Type::Ident(s)).collect(),
                            Box::new(Type::Ident(name.clone())), 
                        ))
                    };

                    let inputt = members.into_iter()
                        .map(|(_, t)| t.clone())
                        .collect::<Vec<_>>();

                    let inputt = match inputt.len() {
                        0 => Box::new(Type::Unit),
                        1 => Box::new(inputt.into_iter().next().unwrap()),
                        _ => Box::new(Type::Tuple(inputt))
                    };

                    constructors.insert(
                        name.clone(),
                        Type::ForAll(
                            args.clone(),
                            Box::new(Type::Arrow(
                                inputt,
                                outt,
                            )),
                        )
                    );
                }
            }
        }

        let mut defs = HashMap::new();

        // Transform each definition into it's intermediate representation
        tree.defs.into_iter()
            .for_each(|(name, def)| {
                defs.insert(name, MIRExpression::from(def, &constructors));
            });

        // Convert each list of function definitions into a lambda match expression
        let mut funcs = HashMap::new();
        tree.funcs.into_iter()
            .for_each(|(name, defs)| {
                let v = "arg.0".to_string();

                let r = defs[0].range;
                let r = defs.iter().fold(r, |r1, e| r1.add(e.range));

                funcs.insert(name, MIRExpression::Lambda1(
                    v.clone(),
                    Box::new(MIRExpression::Match(
                        Box::new(MIRExpression::Identifier(v, r, None)), 
                        defs.into_iter().map(|def| {
                            (def.args.trans_cons(&constructors), MIRExpression::from(def.body, &constructors))
                        }).collect(),
                        r,
                        None
                    )),
                    r,
                    None
                ));
            });


        Self {
            external: tree.external,
            types: tree.types,
            typedefs: tree.typedefs,
            funcs,
            defs,
            constructors,
            declarations,
            structs
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum MIRExpression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String, Range, Option<Type>),

    /// A tuple of expressions
    Tuple(Vec<MIRExpression>, Range, Option<Type>),

    /// A list of expressions
    List(Vec<MIRExpression>, Range, Option<Type>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<MIRExpression>, Vec<(Pattern, MIRExpression)>, Range, Option<Type>),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<MIRExpression>, Box<MIRExpression>, Range, Option<Type>),

    /// Get the member of a struct
    Member(Box<MIRExpression>, String, Range, Option<Type>),

    /// A lambda expression with pattern args and an expression body
    Lambda1(String, Box<MIRExpression>, Range, Option<Type>),

    // Constant Fields
    Num(u64, Range, Option<Type>),    // A Number Literal
    Str(String, Range, Option<Type>), // A String Literal
    Unit(Range, Option<Type>)
}

impl MIRExpression {
    fn from(tree: Expression, cons: &HashMap<String, Type>) -> Self {
        match tree {
            Expression::Num(n, r) => Self::Num(n, r, Some(Type::I32)),
            Expression::Str(s, r) => Self::Str(s, r, Some(Type::Str)),
            Expression::Unit(r) => Self::Unit(r, Some(Type::Unit)),
            Expression::Identifier(i, r) => Self::Identifier(i, r, None),
            Expression::ExprList(es, r) => Self::List(es.into_iter().map(|e| MIRExpression::from(e, cons)).collect(), r, None),
            Expression::Tuple(es, r) => Self::Tuple(es.into_iter().map(|e| MIRExpression::from(e, cons)).collect(), r, None),
            Expression::Match(m, cases, r) => Self::Match(
                Box::new(MIRExpression::from(*m, cons)),
                cases.into_iter().map(|(p, e)| (p.trans_cons(cons), MIRExpression::from(e, cons))).collect(),
                r,
                None
            ),
            Expression::Call(f, args, r) => Self::Call(
                Box::new(MIRExpression::from(*f, cons)),
                Box::new(MIRExpression::from(*args, cons)),
                r,
                None
            ),
            Expression::Member(t, variant, r) => {
                if let Expression::Identifier(t, r) = *t {
                    if cons.contains_key(&format!("{t}.{variant}")) {
                        MIRExpression::Call(
                            Box::new(MIRExpression::Identifier(format!("{t}.{variant}"), r, None)), 
                            Box::new(MIRExpression::Unit(r, Some(Type::Unit))),
                            r, None)
                    } else {
                        MIRExpression::Member(Box::new(MIRExpression::Identifier(t, r, None)), variant, r, None)
                    }
                } else {
                    MIRExpression::Member(Box::new(MIRExpression::from(*t, cons)), variant, r, None)
                }
            }
            Expression::Lambda(pat, body, lamrange) => {
                match pat.trans_cons(cons) {
                    Pattern::Var(s, _, t) => Self::Lambda1(s, Box::new(MIRExpression::from(*body, cons)), lamrange, None),
                    Pattern::Tuple(ps, rtup1, t) => {
                        let mut i = ps.into_iter();
                        let first = i.next().unwrap();
                        let rest: Vec<_> = i.collect();

                        if rest.is_empty() {
                            let l = Expression::Lambda(first, body, lamrange);
                            MIRExpression::from(l, cons)
                        } else {
                            let r = rest[0].range();
                            let rtup = rest.iter().fold(r, |r1, e| r1.add(e.range()));
                            let r = r.add(body.range());
                            let l = Expression::Lambda(Pattern::Tuple(rest, rtup, None), body, r);
                            let r = rtup1.add(l.range());
                            let l = Expression::Lambda(first, Box::new(l), r);
                            MIRExpression::from(l, cons)
                        }
                    }
                    _ => panic!()
                }
            },
            Expression::Let(pat, val, body, r) => Self::Match(
                Box::new(MIRExpression::from(*val, cons)),
                vec![(pat.trans_cons(cons), MIRExpression::from(*body, cons))],
                r,
                None
            ),
            Expression::If(cond, then, els, r) => {
                let r2 = cond.range();
                Self::Match(
                    Box::new(MIRExpression::from(*cond, cons)),
                    vec![
                        (Pattern::Cons("true".into(), Box::new(Pattern::Unit(r2, Some(Type::Unit))), r2, None), MIRExpression::from(*then, cons)),
                        (Pattern::Cons("false".into(), Box::new(Pattern::Unit(r2, Some(Type::Unit))), r2, None), MIRExpression::from(*els, cons)),
                    ],
                    r,
                    None
            )}
        }
    }

    pub fn range(&self) -> Range {
        match self {
            Self::Identifier(_, r, _) => r,
            Self::Num(_, r, _) => r,
            Self::Str(_, r, _) => r,
            Self::Unit(r, _) => r,
            Self::List(_, r, _) => r,
            Self::Tuple(_, r, _) => r,
            Self::Match(_, _, r, _) => r,
            Self::Call(_, _, r, _) => r,
            Self::Lambda1(_, _, r, _) => r,
            Self::Member(_, _, r, _) => r,
        }.clone()
    }
    
    pub fn ty(&self) -> Type {
        match self {
            Self::Identifier(_, _, t) => t,
            Self::Num(_, _, t) => t,
            Self::Str(_, _, t) => t,
            Self::Unit(_, t) => t,
            Self::List(_, _, t) => t,
            Self::Tuple(_, _, t) => t,
            Self::Match(_, _, _, t) => t,
            Self::Call(_, _, _, t) => t,
            Self::Lambda1(_, _, _, t) => t,
            Self::Member(_, _, _, t) => t,
        }.clone().unwrap()
    }

    pub fn set_type(&mut self, ty: Type) {
        match self {
            Self::Identifier(_, _, t) => *t = Some(ty),
            Self::Num(_, _, t) => *t = Some(ty),
            Self::Str(_, _, t) => *t = Some(ty),
            Self::Unit(_, t) => *t = Some(ty),
            Self::List(_, _, t) => *t = Some(ty),
            Self::Tuple(_, _, t) => *t = Some(ty),
            Self::Match(_, _, _, t) => *t = Some(ty),
            Self::Call(_, _, _, t) => *t = Some(ty),
            Self::Lambda1(_, _, _, t) => *t = Some(ty),
            Self::Member(_, _, _, t) => *t = Some(ty),
        }
    }

    pub fn apply(&mut self, subs: &Theta) {
        let term = self.ty().to_term();
        let unterm = apply_unifier(term, subs);
        self.set_type(Type::from_term(unterm));

        match self {
            Self::List(a, _, _) => a.iter_mut().for_each(|e| e.apply(subs)),
            Self::Tuple(a, _, _) => a.iter_mut().for_each(|e| e.apply(subs)),
            Self::Match(a, b, _, _) => {
                a.apply(subs);

                for (pat, e) in b {
                    pat.apply(subs);
                    e.apply(subs);
                }
            }
            Self::Call(a, b, ..) => {
                a.apply(subs);
                b.apply(subs);
            }
            Self::Lambda1(_, b, ..) => {
                b.apply(subs);
            }
            Self::Member(a, ..) => {
                a.apply(subs);
            }
            _ => {}
        }
    }
}

impl Pattern {
    fn trans_cons(self, cons: &HashMap<String, Type>) -> Self {
        match self {
            Self::Var(x, r, t) => {
                if cons.contains_key(&x) {
                    Self::Cons(x, Box::new(Self::Unit(r, Some(Type::Unit))), r, t)
                } else {
                    Self::Var(x, r, t)
                }
            }
            a => a
        }
    }

    fn apply(&mut self, subs: &Theta) {
        let term = self.ty().to_term();
        let unterm = apply_unifier(term, subs);
        self.set_type(Type::from_term(unterm));

        match self {
            Pattern::Cons(_, a, _, _) => {
                a.apply(subs);
            },
            Pattern::Tuple(a, _, _) => {
                a.iter_mut().for_each(|e| e.apply(subs))
            },
            _ => {}
        }
    }
}
