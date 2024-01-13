use std::collections::HashMap;
use std::collections::HashSet;

use crate::lexer::Lexeme;
use crate::lexer::LexemeFeed;
use crate::lexer::Lexer;
use crate::lexer::TokenStream;
use crate::Token;

use crate::parse_tree::Constraint;
use crate::parse_tree::{
    DataDecl, Expression, FunctionDef, Impl, ParseTree, Pattern, QualType, Type, TypeCons, TypeFun,
    Vis,
};

use lazy_static::lazy_static;

lazy_static! {
    static ref PRELUDE: ParseTree = {
        let s = include_str!("./prelude.st");
        let mut l = Lexer::default();
        let mut tokens = l.lex(s).unwrap();

        let me = ParseTree {
            types: HashMap::new(),
            type_aliases: HashMap::new(),
            aliases: HashMap::new(),
            typedecls: HashMap::new(),
            funcs: HashMap::new(),
            defs: HashMap::new(),
            external: HashSet::new(),
            imports: HashSet::new(),
            import_idents: HashSet::new(),
            typefuns: HashMap::new(),
            impls: Vec::new(),
            private_impl_map: HashMap::new()
        };
        // ParseTree::parse_with(&mut tokens, me).unwrap()
        me
    };
}

impl ParseTree {
    pub fn parse(t: &mut TokenStream) -> Result<Self, String> {
        Self::parse_with(t, PRELUDE.clone())
    }

    pub fn parse_with(t: &mut TokenStream, mut me: Self) -> Result<Self, String> {
        loop {
            // This is wrong but we are going to roll with it for now
            let is_pub = if t.consume(Token::Pub).is_some() {
                Vis::Public
            } else {
                Vis::Private
            };

            match t.peek() {
                Some(Lexeme {
                    token: Token::Alias,
                }) => {
                    t.assert(Token::Alias)?;
                    t.assert(Token::Type)?;

                    let name = t.ident()?;

                    t.assert(Token::Assign)?;

                    let ty = Type::parse(t)?;

                    me.type_aliases.insert(name, ty);
                }
                Some(Lexeme { token: Token::Impl }) => {
                    t.assert(Token::Impl)?;
                    let name = t.ident()?;

                    let gen_args = parse_genargs(t)?;
                    let mut args = vec![];
                    t.assert(Token::LParen)?;
                    while let Ok(ty) = QualType::parse(t) {
                        args.push(ty);
                        if t.consume(Token::Comma).is_none() {
                            break;
                        }
                    }
                    t.assert(Token::RParen)?;

                    let mut funcs = vec![];
                    while t.peek()
                        == Some(&Lexeme {
                            token: Token::Ident(name.clone()),
                        })
                    {
                        let name = t.ident()?;
                        let func = FunctionDef::parse(t, name, &me.imports)?;
                        funcs.push(func);
                    }

                    me.impls.push(Impl {
                        fn_name: name,
                        gen_args,
                        args,
                        body: funcs,
                    });
                }
                Some(Lexeme {
                    token: Token::Typefn,
                }) => {
                    t.assert(Token::Typefn)?;

                    let name = t.ident()?;

                    let mut args = vec![];
                    t.assert(Token::LParen)?;
                    while let Ok(id) = t.ident() {
                        args.push(id);
                        if t.consume(Token::Comma).is_none() {
                            break;
                        }
                    }
                    t.assert(Token::RParen)?;
                    t.assert(Token::Assign)?;

                    let ty = Type::parse(t)?;

                    me.typefuns.insert(
                        name.clone(),
                        (
                            is_pub,
                            TypeFun {
                                name,
                                vars: args,
                                ty,
                            },
                        ),
                    );
                }
                Some(Lexeme {
                    token: Token::Import,
                }) => {
                    t.assert(Token::Import)?;
                    let mut namespace = t.ident()?;
                    while t.consume(Token::Dot).is_some() {
                        namespace.push_str(".");
                        namespace.push_str(&t.ident()?);
                    }

                    me.imports.insert(namespace);
                }
                Some(Lexeme { token: Token::From }) => {
                    t.assert(Token::From)?;
                    let mut ns = t.ident()?;
                    while t.consume(Token::Dot).is_some() {
                        ns.push_str(".");
                        ns.push_str(&t.ident()?);
                    }

                    me.imports.insert(ns.clone());
                    t.assert(Token::Import)?;

                    loop {
                        let item = t.ident()?;

                        if t.consume(Token::As).is_some() {
                            let alias = t.ident()?;
                            me.aliases.insert(alias.clone(), format!("{ns}.{item}"));
                        } else {
                            me.aliases.insert(item.clone(), format!("{ns}.{item}"));
                        }

                        if !t.consume(Token::Comma).is_some() {
                            break;
                        }
                    }
                }
                Some(Lexeme {
                    token: Token::Extern,
                    ..
                }) => {
                    t.assert(Token::Extern)?;

                    let name = t.ident()?;
                    t.assert(Token::Colon)?;

                    let ty = Type::parse(t)?;
                    me.typedecls
                        .insert(name.clone(), (is_pub, QualType(vec![], ty)));
                    me.external.insert(name);
                }
                Some(Lexeme {
                    token: Token::Type, ..
                }) => {
                    // Either a typedecl or datadecl
                    t.assert(Token::Type)?;

                    let name = t.ident()?;
                    let args = parse_genargs(t)?;

                    t.assert(Token::Assign)?;
                    let ty = DataDecl::parse(t, name.clone(), args)?;
                    me.types.insert(name, (is_pub, ty));
                }
                Some(Lexeme {
                    token: Token::Unsafe,
                }) => {
                    t.assert(Token::Unsafe)?;
                    let name = t.ident()?;
                    t.assert(Token::Colon)?;

                    let QualType(cons, t) = QualType::parse(t)?;

                    me.typedecls
                        .insert(name, (is_pub, QualType(cons, Type::Unsafe(Box::new(t)))));
                }
                Some(Lexeme {
                    token: Token::Ident(_),
                    ..
                }) => {
                    let name = t.ident()?;

                    match t.peek() {
                        Some(Lexeme {
                            token: Token::LParen,
                        }) => {
                            let func = FunctionDef::parse(t, name, &me.imports)?;
                            if let Some(f) = me.funcs.get_mut(&func.name) {
                                f.push(func);
                            } else {
                                me.funcs.insert(func.name.clone(), vec![func]);
                            }
                        }
                        Some(Lexeme {
                            token: Token::Colon,
                        }) => {
                            t.assert(Token::Colon)?;
                            let ty = QualType::parse(t)?;
                            me.typedecls.insert(name, (is_pub, ty));
                        }
                        Some(Lexeme {
                            token: Token::Assign,
                        }) => {
                            let expr = Expression::parse(t)?.extract_ns(&me.imports);
                            me.defs.insert(name, expr);
                        }
                        _ => panic!("ahh"),
                    }
                }
                Some(a) => return Err(format!("Unexpected token in declaration: '{:?}'", a.token)),
                None => break,
            }
        }

        Ok(me)
    }
}

fn parse_genargs(t: &mut TokenStream) -> Result<Vec<String>, String> {
    if t.consume(Token::LArrow).is_some() {
        let mut args = vec![];
        while !t.test(Token::RArrow) {
            // t.assert(Token::Quote)?;
            args.push(t.ident()?);

            if t.consume(Token::Comma).is_none() {
                break;
            }
        }

        t.assert(Token::RArrow)?;

        Ok(args)
    } else {
        Ok(vec![])
    }
}

impl DataDecl {
    fn parse(t: &mut TokenStream, name: String, args: Vec<String>) -> Result<Self, String> {
        let mut cons = Vec::new();
        let con = TypeCons::parse(t)?;
        cons.push(con);

        while t.consume(Token::Bar).is_some() {
            let con = TypeCons::parse(t)?;
            cons.push(con);
        }

        Ok(Self(name, args, cons))
    }
}

impl TypeCons {
    fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let name = t.ident()?;

        let args = if t.test(Token::LParen) {
            Type::parse(t)?
        } else {
            Type::Unit
        };

        Ok(Self { name, args })
    }
}

impl FunctionDef {
    fn parse(t: &mut TokenStream, name: String, ns: &HashSet<String>) -> Result<Self, String> {
        // Force function def to start with open paren, but don't consume
        if !t.test(Token::LParen) {
            // Guaranteed to error
            t.assert(Token::LParen)?;
        }

        let args = Pattern::parse(t)?;

        t.assert(Token::Assign)?;

        let mut body = Expression::parse(t)?.extract_ns(ns);

        if t.consume(Token::Where).is_some() {
            let p = Pattern::parse(t)?;
            t.assert(Token::Assign)?;
            let e = Expression::parse(t)?;

            let mut bindings = vec![(p, e)];

            while t.consume(Token::Bar).is_some() {
                let p = Pattern::parse(t)?;
                t.assert(Token::Assign)?;
                let e = Expression::parse(t)?;
                bindings.push((p, e));
            }
            bindings.reverse();

            for (p, e) in bindings {
                body = Expression::Let(p, Box::new(e), Box::new(body));
            }
        }

        return Ok(FunctionDef { name, args, body });
    }
}

impl QualType {
    // a ForAll Type looks like a list of constraints,
    // an arrow, and then a type. We have to test to see
    // if we are parsing type constraints before we can
    // really know what we are parsing.
    fn parse(t: &mut TokenStream) -> Result<Self, String> {
        // Try to parse constraint: ident ( vars... ) =>
        if let Ok(i) = t.ident() {
            if t.consume(Token::LParen).is_some() {
                // we are for sure parsing a constraint list now
                let mut cs = vec![];
                let mut c = vec![];

                // finish parsing the first constraint
                while !t.test(Token::RParen) {
                    c.push(Type::parse(t)?);
                    if t.consume(Token::Comma).is_none() {
                        break;
                    }
                }
                cs.push(Constraint(i, c));
                t.assert(Token::RParen)?;

                // now parse the rest of the optional + constraints
                while t.consume(Token::Plus).is_some() {
                    let name = t.ident()?;
                    let mut c = vec![];
                    t.assert(Token::LParen)?;

                    while !t.test(Token::RParen) {
                        c.push(Type::parse(t)?);
                        if t.consume(Token::Comma).is_none() {
                            break;
                        }
                    }
                    t.assert(Token::RParen)?;
                    cs.push(Constraint(name, c));
                }

                // =>
                t.assert(Token::FatArrow)?;

                Ok(QualType(cs, Type::parse(t)?))
            } else {
                // we are not parsing a constraint list, parse as type
                // we push the tokens back onto the lexer before parsing
                t.push_front(Lexeme {
                    token: Token::Ident(i),
                });
                Ok(QualType(vec![], Type::parse(t)?))
            }
        } else {
            let t = Type::parse(t)?;
            Ok(QualType(vec![], t))
        }
    }
}

impl Type {
    pub fn from_str(s: &str) -> Result<Self, String> {
        let mut l = Lexer::default();
        let mut tokens = l.lex(s)?;
        Type::parse(&mut tokens)
    }

    fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let cont = Self::parse_tuple(t)?;

        if t.consume(Token::Arrow).is_some() {
            let end = Self::parse(t)?;

            Ok(Self::Arrow(Box::new(cont), Box::new(end)))
        } else {
            Ok(cont)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Self, String> {
        if t.consume(Token::LParen).is_some() {
            if t.consume(Token::RParen).is_some() {
                // Not a tuple, an empty type
                return Ok(Self::Unit);
            }

            let mut inner = vec![Self::parse(t)?];

            // Parse comma separated fields
            while t.consume(Token::Comma).is_some() {
                inner.push(Self::parse(t)?);
            }

            t.assert(Token::RParen)?;

            if inner.len() == 1 {
                Ok(inner.pop().unwrap())
            } else {
                Ok(Self::Tuple(inner))
            }
        } else {
            Ok(Self::parse_list(t)?)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Result<Self, String> {
        if t.consume(Token::LBrace).is_some() {
            let inner = Self::parse(t)?;

            t.assert(Token::RBrace)?;

            Ok(Self::Generic(
                vec![inner],
                Box::new(Self::Ident("list".to_string())),
            ))
        } else {
            Self::parse_generic(t)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Result<Self, String> {
        let base = Self::parse_base(t)?;

        if t.consume(Token::LArrow).is_some() {
            let mut vars = Vec::new();
            vars.push(Self::parse(t)?);

            while t.consume(Token::Comma).is_some() {
                vars.push(Self::parse(t)?);
            }

            t.assert(Token::RArrow)?;

            Ok(Self::Generic(vars, Box::new(base)))
        } else if t.consume(Token::Question).is_some() {
            Ok(Self::Generic(
                vec![base],
                Box::new(Self::Ident("maybe".into())),
            ))
        } else {
            Ok(base)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Self, String> {
        Ok(match t.next() {
            Some(Lexeme {
                token: Token::Quote,
            }) => Type::GenVar(t.ident()?),
            Some(Lexeme {
                token: Token::Ident(mut i),
                ..
            }) => {
                while t.consume(Token::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                Type::Ident(i)
            }
            Some(Lexeme { token: Token::Bool }) => Self::Bool,
            Some(Lexeme {
                token: Token::U8, ..
            }) => Self::U8,
            Some(Lexeme {
                token: Token::U16, ..
            }) => Self::U16,
            Some(Lexeme {
                token: Token::U32, ..
            }) => Self::U32,
            Some(Lexeme {
                token: Token::U64, ..
            }) => Self::U64,
            Some(Lexeme {
                token: Token::I8, ..
            }) => Self::I8,
            Some(Lexeme {
                token: Token::I16, ..
            }) => Self::I16,
            Some(Lexeme {
                token: Token::I32, ..
            }) => Self::I32,
            Some(Lexeme {
                token: Token::I64, ..
            }) => Self::I64,
            Some(a) => return Err(format!("Unexpected token in type: '{}'", a.token.name())),
            None => return Err(format!("Unexpected EOF in type")),
        })
    }
}

impl Expression {
    fn extract_ns(self, ns: &HashSet<String>) -> Self {
        match self {
            Expression::Tuple(es) => {
                Expression::Tuple(es.into_iter().map(|e| e.extract_ns(ns)).collect())
            }
            Expression::Let(p, x, then) => {
                Expression::Let(p, Box::new(x.extract_ns(ns)), Box::new(then.extract_ns(ns)))
            }
            Expression::If(c, a, b) => Expression::If(
                Box::new(c.extract_ns(ns)),
                Box::new(a.extract_ns(ns)),
                Box::new(b.extract_ns(ns)),
            ),
            Expression::Match(e, ps) => Expression::Match(
                Box::new(e.extract_ns(ns)),
                ps.into_iter().map(|(p, e)| (p, e.extract_ns(ns))).collect(),
            ),
            Expression::Call(m, n) => {
                Expression::Call(Box::new(m.extract_ns(ns)), Box::new(n.extract_ns(ns)))
            }
            Expression::Lambda(x, m) => Expression::Lambda(x, Box::new(m.extract_ns(ns))),
            a => a,
        }
    }

    // general parsing strategy for expressions:
    // - start with all the left recursive operators
    // - which fall through to the right recursive operators
    // - which call the base expressions
    //    + base is a little misleading, this includes
    //      ifelse, letin, etc
    //    + anything that has an unambiguous delimiting tokens
    pub fn parse(t: &mut TokenStream) -> Result<Self, String> {
        let and = Self::andexpr(t)?;

        if let Some(()) = t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Result<Self, String> {
        let and = Self::andexpr(t)?;

        if let Some(()) = t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    fn andexpr(t: &mut TokenStream) -> Result<Self, String> {
        let bitor = Self::eqexpr(t)?;

        if let Some(()) = t.consume(Token::And) {
            let end = Self::andexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("and".into())),
                Box::new(Self::Tuple(vec![bitor, end])),
            ))
        } else {
            Ok(bitor)
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Result<Self, String> {
        let rel = Self::relexpr(t)?;

        if let Some(()) = t.consume(Token::NotEqual) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else if let Some(()) = t.consume(Token::Equal) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("eq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else {
            Ok(rel)
        }
    }

    fn relexpr(t: &mut TokenStream) -> Result<Self, String> {
        let conc = Self::addexpr(t)?;

        if let Some(()) = t.consume(Token::LArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("lt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::RArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("gt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::LTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("leq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(Token::GTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("geq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else {
            Ok(conc)
        }
    }

    fn addexpr(t: &mut TokenStream) -> Result<Self, String> {
        let mul = Self::mulexpr(t)?;

        if let Some(()) = t.consume(Token::Plus) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("add".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else if let Some(()) = t.consume(Token::Sub) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("sub".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else {
            Ok(mul)
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Result<Self, String> {
        let pow = Self::powexpr(t)?;

        if let Some(()) = t.consume(Token::Mul) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mul".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(Token::Div) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("div".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(Token::Mod) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("mod".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else {
            Ok(pow)
        }
    }

    fn powexpr(t: &mut TokenStream) -> Result<Self, String> {
        let unary = Self::unary(t)?;

        if let Some(()) = t.consume(Token::Pow) {
            let end = Self::powexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("pow".into())),
                Box::new(Self::Tuple(vec![unary, end])),
            ))
        } else {
            Ok(unary)
        }
    }

    fn unary(t: &mut TokenStream) -> Result<Self, String> {
        if let Some(()) = t.consume(Token::Not) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("not".into())),
                Box::new(un),
            ))
        } else if let Some(()) = t.consume(Token::Sub) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("neg".into())),
                Box::new(un),
            ))
        } else {
            Ok(Self::postfix(t)?)
        }
    }

    fn postfix(t: &mut TokenStream) -> Result<Self, String> {
        let primary = Self::eunsafe(t)?;
        Self::postfix_post(t, primary)
    }

    fn eunsafe(t: &mut TokenStream) -> Result<Self, String> {
        if t.consume(Token::Unsafe).is_some() {
            Ok(Self::Unsafe(Box::new(Self::primary(t)?)))
        } else {
            Self::primary(t)
        }
    }

    fn postfix_post(t: &mut TokenStream, primary: Expression) -> Result<Self, String> {
        let pfix = if t.consume(Token::LParen).is_some() {
            // parse a call with a tuple
            let tup = if let Some(()) = t.consume(Token::RParen) {
                Self::Unit
            } else {
                let mut es = Vec::new();
                let e = Self::parse(t)?;
                es.push(e);

                while t.consume(Token::Comma).is_some() {
                    es.push(Self::parse(t)?);
                }

                t.assert(Token::RParen)?;

                if es.len() == 1 {
                    es.into_iter().next().unwrap()
                } else {
                    Self::Tuple(es)
                }
            };

            Self::Call(Box::new(primary), Box::new(tup))
        } else if t.consume(Token::Concat).is_some() {
            // parse a concat expression
            let end = Self::parse(t)?;
            Self::Call(
                Box::new(Self::Identifier("list.Cons".into())),
                Box::new(Self::Tuple(vec![primary, end])),
            )
        } else if t.consume(Token::Dot).is_some() {
            let func = Expression::Identifier(t.ident()?);

            let mut es = vec![];
            t.assert(Token::LParen)?;

            while !t.test(Token::RParen) {
                es.push(Expression::parse(t)?);
                if t.consume(Token::Comma).is_none() {
                    break;
                }
            }
            t.assert(Token::RParen)?;

            let args = match es.len() {
                0 => primary,
                _ => {
                    es.insert(0, primary);
                    Expression::Tuple(es)
                }
            };

            Expression::Call(Box::new(func), Box::new(args))
        } else if t.consume(Token::Question).is_some() {
            let then = Expression::parse(t)?;

            t.assert(Token::Colon)?;

            let else_ = Expression::parse(t)?;

            Self::If(Box::new(primary), Box::new(then), Box::new(else_))
        } else if t.consume(Token::FatArrow).is_some() {
            // Fancy call with primary as first arg.

            // must be followed by an identifer and then some args
            let f = t.ident()?;

            // Get args in tuple
            let mut args = vec![primary];

            t.assert(Token::LParen)?;
            if let Some(()) = t.consume(Token::RParen) {
            } else {
                args.push(Self::parse(t)?);
                while t.consume(Token::Comma).is_some() {
                    args.push(Self::parse(t)?);
                }
                t.assert(Token::RParen)?;
            }

            let args = Self::Tuple(args);

            Self::Call(Box::new(Self::Identifier(f)), Box::new(args))
        } else if t.consume(Token::Arrow).is_some() {
            // parse lambda expression
            let pat = primary.to_lambda_pattern();
            let end = Self::parse(t)?;

            Self::Lambda(pat, Box::new(end))
        } else {
            return Ok(primary);
        };

        Self::postfix_post(t, pfix)
    }

    fn primary(t: &mut TokenStream) -> Result<Self, String> {
        let next = match t.next() {
            Some(t) => t,
            None => return Err("".to_string()),
        };

        match next {
            Lexeme { token: Token::True } => Ok(Expression::True),
            Lexeme {
                token: Token::False,
            } => Ok(Expression::False),
            // Let statement
            Lexeme { token: Token::Let } => {
                let pat = Pattern::parse(t)?;

                t.assert(Token::Assign)?;

                let e = Self::parse(t)?;

                t.assert(Token::In)?;

                let body = Self::parse(t)?;

                Ok(Self::Let(pat, Box::new(e), Box::new(body)))
            }
            // If statement
            Lexeme { token: Token::If } => {
                let cond = Self::parse(t)?;

                t.assert(Token::Then)?;

                let then = Self::parse(t)?;

                t.assert(Token::Else)?;

                let else_ = Self::parse(t)?;

                Ok(Self::If(Box::new(cond), Box::new(then), Box::new(else_)))
            }
            // Match statement
            Lexeme {
                token: Token::Match,
            } => {
                let match_ = Self::parse(t)?;

                t.assert(Token::With)?;
                t.assert(Token::LBrace)?;

                let pat = Pattern::parse(t)?;
                t.assert(Token::Arrow)?;
                let e = Self::parse(t)?;

                let mut cases = vec![(pat, e)];

                while t.consume(Token::Comma).is_some() {
                    let pat = Pattern::parse(t)?;
                    t.assert(Token::Arrow)?;
                    let e = Self::parse(t)?;
                    cases.push((pat, e));
                }

                t.assert(Token::RBrace)?;

                Ok(Self::Match(Box::new(match_), cases))
            }
            // String literal
            Lexeme {
                token: Token::String(s),
                ..
            } => Ok(Self::cons_from_str(&s)),
            // Number literal
            Lexeme {
                token: Token::Num(n),
                ..
            } => Ok(Self::Num(n)),
            // Identifier
            Lexeme {
                token: Token::Ident(mut i),
                ..
            } => {
                // if the ident is capitalized then this must be a constructor...
                // we might change this later to be part of the naming/resolution step,
                // but for now this is a good approximate
                if i.chars().next().unwrap().is_uppercase() && !t.test(Token::LParen) {
                    Ok(Self::Call(
                        Box::new(Self::Identifier(i)),
                        Box::new(Self::Unit),
                    ))
                } else {
                    // This is where we handle the dot operator on identifiers. By default we assume
                    // namespacing, then during the import step the namespaces
                    // that were never imported get converted into the pipe operator

                    while t.consume(Token::Dot).is_some() {
                        i.push_str(".");
                        i.push_str(&t.ident()?);
                    }

                    Ok(Self::Identifier(i))
                }
            }
            // Tuple
            Lexeme {
                token: Token::LParen,
                ..
            } => {
                if let Some(()) = t.consume(Token::RParen) {
                    Ok(Self::Unit)
                } else {
                    let mut es = Vec::new();
                    let e = Self::parse(t)?;
                    es.push(e);

                    while t.consume(Token::Comma).is_some() {
                        es.push(Self::parse(t)?);
                    }

                    t.assert(Token::RParen)?;

                    if es.len() == 1 {
                        Ok(es.into_iter().next().unwrap())
                    } else {
                        Ok(Self::Tuple(es))
                    }
                }
            }
            // List
            Lexeme {
                token: Token::LBrace,
            } => {
                let mut es = Vec::new();

                while !t.test(Token::RBrace) {
                    es.push(Self::parse(t)?);
                    if t.consume(Token::Comma).is_none() {
                        break;
                    }
                }
                t.assert(Token::RBrace)?;

                Ok(Self::cons_from_es(&es))
            }
            // otherwise error
            a => {
                //panic!("PrimaryExpr: Expected identifier, constant, or expression, found: {:?}", a);
                Err(format!("Expected expression, found '{}'", a.token.name()))
            }
        }
    }

    pub fn cons_from_str(s: &str) -> Self {
        let nums = s
            .chars()
            .map(|c| c as u64)
            .map(|i| Self::Num(i))
            .map(|i| {
                Self::Call(
                    Box::new(Self::Identifier("char.Char".to_string())),
                    Box::new(i),
                )
            })
            .collect::<Vec<_>>();

        Self::cons_from_es(&nums)
    }

    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Call(
                Box::new(Self::Identifier("list.Nil".to_string())),
                Box::new(Self::Unit),
            );
        }

        Self::Call(
            Box::new(Self::Identifier("list.Cons".to_string())),
            Box::new(Self::Tuple(vec![
                es[0].clone(),
                Self::cons_from_es(&es[1..]),
            ])),
        )
    }

    fn to_lambda_pattern(&self) -> Pattern {
        match self {
            Self::Identifier(s) => Pattern::Var(s.clone(), None),
            Self::Tuple(es) => {
                Pattern::Tuple(es.iter().map(|e| e.to_lambda_pattern()).collect(), None)
            }
            Self::Unit => Pattern::Unit(Some(Type::Unit)),
            Self::Call(f, args) => {
                if let Expression::Identifier(s) = &**f {
                    Pattern::Cons(s.clone(), Box::new(args.to_lambda_pattern()), None)
                } else {
                    panic!("lambda what?")
                }
            }
            _ => panic!("ahh"),
        }
    }
}

impl Pattern {
    pub fn cons_from_str(s: &str) -> Self {
        let nums = s
            .chars()
            .map(|c| c as u64)
            .map(|i| Self::Num(i, None))
            .collect::<Vec<_>>();

        Self::cons_from_es(&nums)
    }

    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Cons("list.Nil".to_string(), Box::new(Self::Unit(None)), None);
        }

        Self::Cons(
            "list.Cons".to_string(),
            Box::new(Self::Tuple(
                vec![es[0].clone(), Self::cons_from_es(&es[1..])],
                None,
            )),
            None,
        )
    }

    fn parse(t: &mut TokenStream) -> Result<Pattern, String> {
        let x = Self::parse_base(t)?;

        if t.consume(Token::Concat).is_some() {
            let xs = Self::parse(t)?;
            return Ok(Self::Cons(
                "list.Cons".into(),
                Box::new(Pattern::Tuple(vec![x, xs], None)),
                None,
            ));
        }

        Ok(x)
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Pattern, String> {
        t.assert(Token::LParen)?;
        // We are either the unit type or the tuple type

        if let Some(()) = t.consume(Token::RParen) {
            return Ok(Pattern::Unit(Some(Type::Unit)));
        }

        let mut pats = Vec::new();
        let pat = Pattern::parse(t)?;
        pats.push(pat);

        while let Some(()) = t.consume(Token::Comma) {
            let pat = Pattern::parse(t)?;
            pats.push(pat);
        }

        t.assert(Token::RParen)?;

        if pats.len() == 1 {
            Ok(pats.into_iter().next().unwrap())
        } else {
            Ok(Pattern::Tuple(pats, None))
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Pattern, String> {
        if t.test(Token::LParen) {
            return Self::parse_tuple(t);
        }

        match t.next() {
            Some(Lexeme {
                token: Token::Unsafe,
            }) => Ok(Pattern::Unsafe(Box::new(Self::parse(t)?), None)),
            Some(Lexeme {
                token: Token::LBrace,
                ..
            }) => {
                t.assert(Token::RBrace)?;
                Ok(Pattern::Cons(
                    "list.Nil".to_string(),
                    Box::new(Self::Unit(Some(Type::Unit))),
                    None,
                ))
            }
            Some(Lexeme {
                token: Token::Underscore,
            }) => Ok(Pattern::Any(None)),
            Some(Lexeme {
                token: Token::Num(n),
                ..
            }) => Ok(Pattern::Num(n, Some(Type::I32))),
            Some(Lexeme {
                token: Token::String(s),
                ..
            }) => Ok(Pattern::cons_from_str(&s)),
            Some(Lexeme { token: Token::True }) => Ok(Self::True),
            Some(Lexeme {
                token: Token::False,
            }) => Ok(Self::False),
            Some(Lexeme {
                token: Token::Ident(mut i),
                ..
            }) => {
                while t.consume(Token::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                if i.contains(".") {
                    // This is a namespaced constructor
                    let args = if t.test(Token::LParen) {
                        Pattern::parse_tuple(t)?
                    } else {
                        Pattern::Unit(Some(Type::Unit))
                    };

                    Ok(Pattern::Cons(i, Box::new(args), None))
                } else {
                    // either a variable or a constructor
                    // lets enforce that constructors *must* start with a capital
                    // and that variables have to start with lowercase
                    if i.chars().next().unwrap().is_uppercase() {
                        // This is a namespaced constructor
                        let args = if t.test(Token::LParen) {
                            Pattern::parse_tuple(t)?
                        } else {
                            Pattern::Unit(Some(Type::Unit))
                        };
                        Ok(Pattern::Cons(i, Box::new(args), None))
                    } else {
                        Ok(Pattern::Var(i, None))
                    }
                }
            }
            a => panic!("unexpected token: {a:?} {:?} {:?}", t.next(), t.next()),
        }
    }
}
