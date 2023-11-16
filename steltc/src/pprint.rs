// use crate::lir::LIRExpression;
use crate::mir::MIRExpression;
use crate::parse_tree::Pattern;

#[derive(Clone, PartialEq, Eq)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    fn count(&self) -> usize {
        match self {
            SExpr::Atom(_) => 1,
            SExpr::List(es) => es.iter().map(|e| e.count()).sum(),
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            SExpr::Atom(s) => s.clone(),
            SExpr::List(es) => {
                let mut s = String::new();
                s.push('(');

                let len = es.len();
                if len >= 1 && es[0] == SExpr::Atom("quote".to_string()) {
                    let mut s = SExpr::List(es[1..].to_vec()).to_string();
                    s.insert(0, '\'');
                    s
                } else {
                    for (i, e) in es.iter().enumerate() {
                        let estr = e.to_string();
                        let estr = estr.replace("\n", "\n  ");
                        s.push_str(&estr);

                        if i != len - 1 {
                            if e.count() <= 2 {
                                s.push(' ');
                            } else {
                                s.push('\n');
                            }
                        }
                    }

                    s.push(')');
                    s
                }
            }
        }
    }
}

impl MIRExpression {
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            MIRExpression::Ref(t, _) => {
                SExpr::List(vec![SExpr::Atom("&".to_string()), t.to_sexpr()])
            }
            MIRExpression::True => SExpr::Atom("True".to_string()),
            MIRExpression::False => SExpr::Atom("False".to_string()),
            MIRExpression::Identifier(s, _) => SExpr::Atom(s.clone()),
            MIRExpression::Tuple(es, _) => {
                let mut inner = vec![SExpr::Atom("quote".to_string())];
                inner.extend(es.iter().map(|e| e.to_sexpr()));
                SExpr::List(inner)
            }
            MIRExpression::Match(e, ps, _) => {
                let mut inner = vec![SExpr::Atom("match".to_string()), e.to_sexpr()];

                for (p, e) in ps {
                    inner.push(SExpr::List(vec![p.to_sexpr(), e.to_sexpr()]))
                }

                SExpr::List(inner)
            }
            MIRExpression::Call(f, args, _) => SExpr::List(vec![f.to_sexpr(), args.to_sexpr()]),
            MIRExpression::Lambda1(x, m, _) => SExpr::List(vec![
                SExpr::Atom("lambda".to_string()),
                x.clone()
                    .map(|s| SExpr::Atom(s))
                    .unwrap_or(SExpr::List(vec![])),
                m.to_sexpr(),
            ]),
            MIRExpression::Num(n, _) => SExpr::Atom(n.to_string()),
            MIRExpression::Unit(_) => SExpr::List(vec![]),
        }
    }
}

// impl LIRExpression {
//     fn to_sexpr(&self) -> SExpr {
//         match self {
//             Self::Identifier(s, t) => SExpr::Atom(format!("{}: {}", s, t)),
//             Self::Call(f, args, t) => SExpr::List(vec![
//                 SExpr::Atom(format!("call: {t}")),
//                 f.to_sexpr(),
//                 args.to_sexpr(),
//             ]),
//             Self::ExternCall(f, args, t) => {
//                 let mut inner = vec![
//                     SExpr::Atom(format!("externcall: {t}")),
//                     SExpr::Atom(f.clone()),
//                 ];

//                 for e in args {
//                     inner.push(e.to_sexpr());
//                 }

//                 SExpr::List(inner)
//             }
//             Self::GlobalCall(f, args, t) => SExpr::List(vec![
//                 SExpr::Atom(format!("globalcall: {t}")),
//                 SExpr::Atom(f.clone()),
//                 args.to_sexpr(),
//             ]),
//             Self::Lambda1(x, m, t) => SExpr::List(vec![
//                 SExpr::Atom(format!("lambda: {t}")),
//                 x.map(|s| SExpr::Atom(s.clone()))
//                     .unwrap_or(SExpr::List(vec![])),
//                 m.to_sexpr(),
//             ]),
//             Self::Let1(x, e, body, t) => SExpr::List(vec![SExpr::Atom(format!("let: {t}"))]),
//         }
//     }
// }

impl Pattern {
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            Self::True => SExpr::Atom("True".to_string()),
            Self::False => SExpr::Atom("False".to_string()),
            Self::Unit(_) => SExpr::List(vec![]),
            Self::Num(n, _) => SExpr::Atom(n.to_string()),
            Self::Var(x, _) => SExpr::Atom(x.clone()),
            Self::Tuple(ps, _) => {
                let mut inner = vec![SExpr::Atom("tuple".to_string())];
                for p in ps {
                    inner.push(p.to_sexpr());
                }

                SExpr::List(inner)
            }
            Self::Cons(f, args, _) => SExpr::List(vec![SExpr::Atom(f.clone()), args.to_sexpr()]),
            Self::Any(_) => SExpr::Atom("_".to_string()),
        }
    }
}
