use std::collections::HashMap;

use crate::parse_tree::{
    ParseTree,
    Expression,
    Type,
    DataDecl,
    Trait,
    Pattern
};


#[derive(Debug)]
pub struct MIRTree {
    pub traits: HashMap<String, Trait>,
    pub types: HashMap<String, DataDecl>,
    pub typedefs: HashMap<String, Type>,
    pub funcs: HashMap<String, MIRExpression>,
    pub defs: HashMap<String, MIRExpression>
}

impl MIRTree {
    pub fn from(mut tree: ParseTree) -> Self {
        // For each trait implementation, use the trait as a template with
        // the implemented type as the substitution. Insert new functions
        // into funcs
        for i in tree.impls {
            let tr = tree.traits.get(&i.trait_name).unwrap();
            let tname = i.for_type.name();

            // Generate new typedef for each typedef in types with a unique named
            // prefixed by name of this impl type
            let mut subs = HashMap::new();
            for (name, t) in tr.types.iter() {
                let n: u16 = rand::random();
                let new_name = format!("{}_{}$${}", tname, name, n);
                tree.typedefs.insert(new_name.clone(), t.clone());
                subs.insert(name, new_name);
            }
        }

        let mut defs = HashMap::new();

        // Transform each definition into it's intermediate representation
        tree.defs.into_iter()
            .for_each(|(name, def)| {
                defs.insert(name, MIRExpression::from(def));
            });

        // Convert each list of function definitions into a lambda match expression
        let mut funcs = HashMap::new();
        tree.funcs.into_iter()
            .for_each(|(name, defs)| {
                let n: u16 = rand::random();
                let v = format!("var$${}", n);

                funcs.insert(name, MIRExpression::Lambda(
                        Pattern::Var(v.clone()),
                        Box::new(MIRExpression::Match(
                            Box::new(MIRExpression::Identifier(v)), 
                            defs.into_iter().map(|def| {
                                (def.args, MIRExpression::from(def.body))
                            }).collect()))));
            });
        
        Self {
            traits: tree.traits,
            types: tree.types,
            typedefs: tree.typedefs,
            funcs,
            defs
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum MIRExpression {
    /// An identifier that we can evaluate.
    /// usually a variable that was defined previously
    Identifier(String),

    /// A tuple of expressions
    Tuple(Vec<MIRExpression>),

    /// A list of expressions
    List(Vec<MIRExpression>),

    /// Test a list of patterns against an expression, returning the expression that matches
    Match(Box<MIRExpression>, Vec<(Pattern, MIRExpression)>),

    /// Call the function with args
    /// Can be a global function, a lambda, or a constructor
    Call(Box<MIRExpression>, Vec<MIRExpression>),

    /// A lambda expression with pattern args and an expression body
    Lambda(Pattern, Box<MIRExpression>),

    // Constant Fields
    Num(u64),    // A Number Literal
    Str(String), // A String Literal
    EmptyList,
    Unit
}

impl MIRExpression {
    fn from(tree: Expression) -> Self {
        match tree {
            Expression::Num(n) => Self::Num(n),
            Expression::Str(s) => Self::Str(s),
            Expression::EmptyList => Self::EmptyList,
            Expression::Unit => Self::Unit,
            Expression::Identifier(i) => Self::Identifier(i),
            Expression::ExprList(es) => Self::List(es.into_iter().map(MIRExpression::from).collect()),
            Expression::Tuple(es) => Self::Tuple(es.into_iter().map(MIRExpression::from).collect()),
            Expression::Match(m, cases) => Self::Match(
                Box::new(MIRExpression::from(*m)),
                cases.into_iter().map(|(p, e)| (p, MIRExpression::from(e))).collect()
            ),
            Expression::Call(f, args) => Self::Call(
                Box::new(MIRExpression::from(*f)),
                args.into_iter().map(MIRExpression::from).collect()
            ),
            Expression::Lambda(pat, body) => Self::Lambda(pat, Box::new(MIRExpression::from(*body))),
            Expression::Let(pat, val, body) => Self::Match(
                Box::new(MIRExpression::from(*val)),
                vec![(pat, MIRExpression::from(*body))]
            ),
            Expression::If(cond, then, els) => Self::Match(
                Box::new(MIRExpression::from(*cond)),
                vec![
                    (Pattern::Cons("true".into(), Box::new(Pattern::Unit)), MIRExpression::from(*then)),
                    (Pattern::Cons("false".into(), Box::new(Pattern::Unit)), MIRExpression::from(*els)),
                ]
            )
        }
    }
}
