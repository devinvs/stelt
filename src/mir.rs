use std::collections::HashMap;

use crate::parse_tree::{
    ParseTree,
    Expression,
    Type,
    DataDecl,
    Trait,
    Pattern
};

use crate::error::Range;


#[derive(Debug)]
pub struct MIRTree {
    pub traits: HashMap<String, Trait>,
    pub types: HashMap<String, DataDecl>,
    pub typedefs: HashMap<String, Type>,
    pub structs: HashMap<String, HashMap<String, Type>>,
    pub funcs: HashMap<String, MIRExpression>,
    pub defs: HashMap<String, MIRExpression>,

    pub constructors: HashMap<String, Type>,
    pub declarations: HashMap<String, Type>
}

impl MIRTree {
    pub fn from(mut tree: ParseTree) -> Self {
        // For each trait implementation, use the trait as a template with
        // the implemented type as the substitution. Insert new functions
        // into funcs
        for i in tree.impls {
            let tr = tree.traits.get(&i.trait_name).unwrap();

            // Generate new typedef for each typedef in types with a unique named
            // prefixed by name of this impl type
            let mut subs = HashMap::new();
            for (name, t) in tr.types.iter() {
                let n: u16 = rand::random();
                let new_name = format!("{}$${}", name, n);
                tree.typedefs.insert(new_name.clone(), t.clone());
                subs.insert(name, new_name);
            }
        }

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
                DataDecl::Sum(_, args, cons, range) => {
                    for cons in cons {
                        let outt = if args.len() == 0 {
                            Box::new(Type::Ident(name.clone(), range.clone()))
                        } else {
                            Box::new(Type::Generic(
                                args.clone().into_iter().map(|s| Type::Ident(s, range.clone())).collect(),
                                Box::new(Type::Ident(name.clone(), range.clone())), 
                                range.clone()
                            ))
                        };

                        constructors.insert(
                            format!("{name}.{}", cons.name),
                            Type::ForAll(
                                args.clone(),
                                Box::new(Type::Arrow(
                                    Box::new(cons.args.clone()),
                                    outt,
                                    range.clone())
                                ),
                                range.clone()
                            )
                        );
                    }
                }
                DataDecl::Product(_, args, members, range) => {
                    // Add an entry into the structs map
                    let mut m = HashMap::new();
                    members.iter().for_each(|(n, t)| {m.insert(n.clone(), t.clone());});

                    structs.insert(name.clone(), m);

                    // add constructor
                    let outt = if args.len() == 0 {
                        Box::new(Type::Ident(name.clone(), range.clone()))
                    } else {
                        Box::new(Type::Generic(
                            args.clone().into_iter().map(|s| Type::Ident(s, range.clone())).collect(),
                            Box::new(Type::Ident(name.clone(), range.clone())), 
                            range.clone()
                        ))
                    };

                    let inputt = members.into_iter()
                        .map(|(_, t)| t.clone())
                        .collect::<Vec<_>>();

                    let inputt = match inputt.len() {
                        0 => Box::new(Type::Unit(range.clone())),
                        1 => Box::new(inputt.into_iter().next().unwrap()),
                        _ => Box::new(Type::Tuple(inputt, range.clone()))
                    };

                    constructors.insert(
                        name.clone(),
                        Type::ForAll(
                            args.clone(),
                            Box::new(Type::Arrow(
                                inputt,
                                outt,
                                range.clone()
                            )),
                            range.clone()
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
                let n: u16 = rand::random();
                let v = format!("var$${}", n);

                let r = defs[0].range;
                let r = defs.iter().fold(r, |r1, e| r1.add(e.range));

                funcs.insert(name, MIRExpression::Lambda1(
                    v.clone(),
                    Box::new(MIRExpression::Match(
                        Box::new(MIRExpression::Identifier(v, r)), 
                        defs.into_iter().map(|def| {
                            (def.args.trans_cons(&constructors), MIRExpression::from(def.body, &constructors))
                        }).collect(),
                        r
                    )),
                    r
                ));
            });


        Self {
            traits: tree.traits,
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
    Identifier(String, Range),

    /// A tuple of expressions
    Tuple(Vec<MIRExpression>, Range),

    /// A list of expressions
    List(Vec<MIRExpression>, Range),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<MIRExpression>, Vec<(Pattern, MIRExpression)>, Range),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<MIRExpression>, Box<MIRExpression>, Range),

    /// Get the member of a struct
    Member(Box<MIRExpression>, String, Range),

    /// A lambda expression with pattern args and an expression body
    Lambda1(String, Box<MIRExpression>, Range),

    // Constant Fields
    Num(u64, Range),    // A Number Literal
    Str(String, Range), // A String Literal
    Unit(Range)
}

impl MIRExpression {
    fn from(tree: Expression, cons: &HashMap<String, Type>) -> Self {
        match tree {
            Expression::Num(n, r) => Self::Num(n, r),
            Expression::Str(s, r) => Self::Str(s, r),
            Expression::Unit(r) => Self::Unit(r),
            Expression::Identifier(i, r) => Self::Identifier(i, r),
            Expression::ExprList(es, r) => Self::List(es.into_iter().map(|e| MIRExpression::from(e, cons)).collect(), r),
            Expression::Tuple(es, r) => Self::Tuple(es.into_iter().map(|e| MIRExpression::from(e, cons)).collect(), r),
            Expression::Match(m, cases, r) => Self::Match(
                Box::new(MIRExpression::from(*m, cons)),
                cases.into_iter().map(|(p, e)| (p.trans_cons(cons), MIRExpression::from(e, cons))).collect(),
                r
            ),
            Expression::Call(f, args, r) => Self::Call(
                Box::new(MIRExpression::from(*f, cons)),
                Box::new(MIRExpression::from(*args, cons)),
                r
            ),
            Expression::Member(t, variant, r) => {
                if let Expression::Identifier(t, r) = *t {
                    if cons.contains_key(&format!("{t}.{variant}")) {
                        MIRExpression::Call(
                            Box::new(MIRExpression::Identifier(format!("{t}.{variant}"), r)), 
                            Box::new(MIRExpression::Unit(r)),
                            r)
                    } else {
                        MIRExpression::Member(Box::new(MIRExpression::Identifier(t, r)), variant, r)
                    }
                } else {
                    MIRExpression::Member(Box::new(MIRExpression::from(*t, cons)), variant, r)
                }
            }
            Expression::Lambda(pat, body, lamrange) => {
                match pat.trans_cons(cons) {
                    Pattern::Var(s, _) => Self::Lambda1(s, Box::new(MIRExpression::from(*body, cons)), lamrange),
                    Pattern::Tuple(ps, rtup1) => {
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
                            let l = Expression::Lambda(Pattern::Tuple(rest, rtup), body, r);
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
                r
            ),
            Expression::If(cond, then, els, r) => {
                let r2 = cond.range();
                Self::Match(
                    Box::new(MIRExpression::from(*cond, cons)),
                    vec![
                        (Pattern::Cons("true".into(), Box::new(Pattern::Unit(r2)), r2), MIRExpression::from(*then, cons)),
                        (Pattern::Cons("false".into(), Box::new(Pattern::Unit(r2)), r2), MIRExpression::from(*els, cons)),
                    ],
                    r
            )}
        }
    }

    pub fn range(&self) -> Range {
        match self {
            Self::Identifier(_, r) => r,
            Self::Num(_, r) => r,
            Self::Str(_, r) => r,
            Self::Unit(r) => r,
            Self::List(_, r) => r,
            Self::Tuple(_, r) => r,
            Self::Match(_, _, r) => r,
            Self::Call(_, _, r) => r,
            Self::Lambda1(_, _, r) => r,
            Self::Member(_, _, r) => r,
        }.clone()
    }
}

impl Pattern {
    fn trans_cons(self, cons: &HashMap<String, Type>) -> Self {
        match self {
            Self::Var(x, r) => {
                if cons.contains_key(&x) {
                    Self::Cons(x, Box::new(Self::Unit(r)), r)
                } else {
                    Self::Var(x, r)
                }
            }
            a => a
        }
    }
}
