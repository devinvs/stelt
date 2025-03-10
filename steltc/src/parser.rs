use std::collections::HashMap;
use std::collections::HashSet;

use crate::error::SrcError;
use crate::lexer::Lexer;
use crate::lexer::Token;
use crate::lexer::TokenStream;
use crate::lexer::TokenType;

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
        let mut tokens = l.lex(&s, &"./prelude.st".into()).unwrap();

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
            private_impl_map: HashMap::new(),
        };
        let me = ParseTree::parse_with(&mut tokens, me).unwrap();
        me
    };
}

impl ParseTree {
    pub fn parse(t: &mut TokenStream) -> Result<Self, Self> {
        Self::parse_with(t, PRELUDE.clone())
    }

    // parse what we can, accumulate errors, recover as necessary
    pub fn parse_with(t: &mut TokenStream, mut me: Self) -> Result<Self, Self> {
        let mut fail = false;

        loop {
            match me.parse_stmt(t) {
                Ok(()) => {
                    // every single stmt must be followed by a newline or eof
                    // newline
                    t.nl_aware();
                    if t.consume(TokenType::NL).is_some() {
                        t.nl_ignore();
                        continue;
                    }
                    t.nl_ignore();

                    // end of file
                    if t.peek().is_none() {
                        break;
                    }

                    // not followed by eof or newline, emit error and
                    // attempt recovery
                    let l = t.next().unwrap();
                    SrcError::new(
                        t.file(),
                        l.pos,
                        l.end(),
                        format!(
                            "expected newline at end of statement, found '{}'",
                            l.ty.name()
                        ),
                    )
                    .print();

                    if me.recover(t).is_err() {
                        break;
                    }
                }
                Err(e) => {
                    e.print();
                    fail = true;

                    if me.recover(t).is_err() {
                        break;
                    }
                }
            }
        }

        if fail {
            Err(me)
        } else {
            Ok(me)
        }
    }

    // attempt to recover after an error. This is super basic.
    // basically skip to the next line until parsing starts working again.
    // we miss the errors inbetween, but probably get print more errors altogether
    // we fail when we hit eof
    fn recover(&mut self, t: &mut TokenStream) -> Result<(), ()> {
        loop {
            // break on end of file
            if t.peek().is_none() {
                return Err(());
            }

            // consume tokens until we hit a newline
            t.nl_aware();
            loop {
                match t.next() {
                    None => return Err(()),
                    Some(Token {
                        ty: TokenType::NL, ..
                    }) => break,
                    _ => {}
                }
            }
            t.nl_ignore();

            // attempt to parse another statement
            match self.parse_stmt(t) {
                Ok(()) => return Ok(()),
                _ => {}
            }
        }
    }

    // parse a single statement, mutating the tree as necessary
    // invariant: if you return an error, the tree must not be altered
    fn parse_stmt(&mut self, t: &mut TokenStream) -> Result<(), SrcError> {
        // This is wrong but we are going to roll with it for now
        let is_pub = if t.consume(TokenType::Pub).is_some() {
            Vis::Public
        } else {
            Vis::Private
        };

        match t.peek() {
            Some(Token {
                ty: TokenType::Alias,
                ..
            }) => {
                t.assert(TokenType::Alias)?;
                t.assert(TokenType::Type)?;

                let name = t.ident()?;

                t.assert(TokenType::Assign)?;

                let ty = Type::parse(t)?;

                self.type_aliases.insert(name, ty);
                Ok(())
            }
            Some(Token {
                ty: TokenType::Impl,
                ..
            }) => {
                t.assert(TokenType::Impl)?;
                let name = t.ident()?;

                let gen_args = parse_genargs(t)?;
                let mut args = vec![];
                t.assert(TokenType::LParen)?;
                while let Ok(ty) = QualType::parse(t) {
                    args.push(ty);
                    if t.consume(TokenType::Comma).is_none() {
                        break;
                    }
                }
                t.assert(TokenType::RParen)?;

                let mut funcs = vec![];
                while t.peek().map(|t| &t.ty) == Some(&TokenType::Ident(name.clone())) {
                    let name = t.ident()?;
                    let func = FunctionDef::parse(t, name, &self.imports)?;
                    funcs.push(func);
                }

                self.impls.push(Impl {
                    fn_name: name,
                    gen_args,
                    args,
                    body: funcs,
                });
                Ok(())
            }
            Some(Token {
                ty: TokenType::Typefn,
                ..
            }) => {
                t.assert(TokenType::Typefn)?;

                let name = t.ident()?;

                let mut args = vec![];
                t.assert(TokenType::LParen)?;
                while let Ok(id) = t.ident() {
                    args.push(id);
                    if t.consume(TokenType::Comma).is_none() {
                        break;
                    }
                }
                t.assert(TokenType::RParen)?;
                t.assert(TokenType::Assign)?;

                let ty = Type::parse(t)?;

                self.typefuns.insert(
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
                Ok(())
            }
            Some(Token {
                ty: TokenType::Import,
                ..
            }) => {
                t.assert(TokenType::Import)?;
                let mut namespace = t.ident()?;

                while t.consume(TokenType::Slash).is_some() {
                    namespace.push_str("/");
                    namespace.push_str(&t.ident()?);
                }

                self.imports.insert(namespace);
                Ok(())
            }
            Some(Token {
                ty: TokenType::From,
                ..
            }) => {
                t.assert(TokenType::From)?;
                let mut ns = t.ident()?;
                while t.consume(TokenType::Slash).is_some() {
                    ns.push_str("/");
                    ns.push_str(&t.ident()?);
                }

                t.assert(TokenType::Import)?;

                let mut aliases = vec![];

                loop {
                    let item = t.ident()?;

                    if t.consume(TokenType::As).is_some() {
                        let alias = t.ident()?;
                        aliases.push((alias, item));
                    } else {
                        aliases.push((item.clone(), item.clone()))
                    }

                    if !t.consume(TokenType::Comma).is_some() {
                        break;
                    }
                }

                for (a, b) in aliases {
                    self.aliases.insert(a, format!("{ns}/{b}"));
                }

                self.imports.insert(ns.clone());
                Ok(())
            }
            Some(Token {
                ty: TokenType::Extern,
                ..
            }) => {
                t.assert(TokenType::Extern)?;

                let name = t.ident()?;
                t.assert(TokenType::Colon)?;

                let ty = Type::parse(t)?;

                self.typedecls
                    .insert(name.clone(), (is_pub, QualType(vec![], ty)));
                self.external.insert(name);
                Ok(())
            }
            Some(Token {
                ty: TokenType::Type,
                ..
            }) => {
                // Either a typedecl or datadecl
                t.assert(TokenType::Type)?;

                let name = t.ident()?;
                let args = parse_genargs(t)?;

                t.assert(TokenType::Assign)?;
                let ty = DataDecl::parse(t, name.clone(), args)?;

                self.types.insert(name, (is_pub, ty));
                Ok(())
            }
            Some(Token {
                ty: TokenType::Ident(_),
                ..
            }) => {
                let name = t.ident()?;

                match t.peek() {
                    Some(Token {
                        ty: TokenType::LParen,
                        ..
                    }) => {
                        let func = FunctionDef::parse(t, name, &self.imports)?;
                        if let Some(f) = self.funcs.get_mut(&func.name) {
                            f.push(func);
                        } else {
                            self.funcs.insert(func.name.clone(), vec![func]);
                        }
                        Ok(())
                    }
                    Some(Token {
                        ty: TokenType::Colon,
                        ..
                    }) => {
                        t.assert(TokenType::Colon)?;
                        let ty = QualType::parse(t)?;
                        self.typedecls.insert(name, (is_pub, ty));
                        Ok(())
                    }
                    Some(Token {
                        ty: TokenType::Assign,
                        ..
                    }) => {
                        t.assert(TokenType::Assign)?;
                        let expr = Expression::parse(t)?.extract_ns(&self.imports);
                        self.defs.insert(name, expr);
                        Ok(())
                    }
                    Some(_) => {
                        let l = t.next().unwrap();
                        Err(SrcError::new(
                            t.file(),
                            l.pos,
                            l.end(),
                            format!(
                                "expected ':', '=', or '(' after identifer, found '{}'",
                                l.ty.name()
                            ),
                        ))
                    }
                    None => Err(SrcError::new(
                        t.file(),
                        t.eof(),
                        t.eof(),
                        "unexpected end of file while parsing type".to_string(),
                    )),
                }
            }
            Some(_) => {
                let l = t.next().unwrap();
                Err(SrcError::new(
                    t.file(),
                    l.pos,
                    l.end(),
                    format!(
                        "unexpected token while parsing statement: '{}'",
                        l.ty.name()
                    ),
                ))
            }
            None => Ok(()),
        }
    }
}

fn parse_genargs(t: &mut TokenStream) -> Result<Vec<String>, SrcError> {
    if t.consume(TokenType::LArrow).is_some() {
        let mut args = vec![];
        while !t.test(TokenType::RArrow) {
            match t.ident() {
                Ok(i) => args.push(i),
                Err(s) => return Err(s),
            }
            if t.consume(TokenType::Comma).is_none() {
                break;
            }
        }

        t.assert(TokenType::RArrow)?;

        Ok(args)
    } else {
        Ok(vec![])
    }
}

impl DataDecl {
    fn parse(t: &mut TokenStream, name: String, args: Vec<String>) -> Result<Self, SrcError> {
        let mut cons = Vec::new();
        let con = TypeCons::parse(t)?;
        cons.push(con);

        while t.consume(TokenType::Bar).is_some() {
            let con = TypeCons::parse(t)?;
            cons.push(con);
        }

        Ok(Self(name, args, cons))
    }
}

impl TypeCons {
    fn parse(t: &mut TokenStream) -> Result<Self, SrcError> {
        let name = t.ident()?;

        let args = if t.test(TokenType::LParen) {
            Type::parse(t)?
        } else {
            Type::Unit
        };

        Ok(Self { name, args })
    }
}

impl FunctionDef {
    fn parse(t: &mut TokenStream, name: String, ns: &HashSet<String>) -> Result<Self, SrcError> {
        // Force function def to start with open paren, but don't consume
        if !t.test(TokenType::LParen) {
            // Guaranteed to error
            t.assert(TokenType::LParen)?;
        }

        let args = Pattern::parse(t)?;

        t.assert(TokenType::Assign)?;

        let mut body = Expression::parse(t)?.extract_ns(ns);

        if t.consume(TokenType::Where).is_some() {
            let p = Pattern::parse(t)?;
            t.assert(TokenType::Assign)?;
            let e = Expression::parse(t)?;

            let mut bindings = vec![(p, e)];

            while t.consume(TokenType::Bar).is_some() {
                let p = Pattern::parse(t)?;
                t.assert(TokenType::Assign)?;
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
    // a QualType looks like a list of constraints,
    // an arrow, and then a type. We have to test to see
    // if we are parsing type constraints before we can
    // really know what we are parsing.
    fn parse(t: &mut TokenStream) -> Result<Self, SrcError> {
        // Try to parse constraint: ident ( vars... ) =>
        if let Ok((i, pos)) = t.ident_tok() {
            if t.consume(TokenType::LParen).is_some() {
                // we are for sure parsing a constraint list now
                let mut cs = vec![];
                let mut c = vec![];

                // finish parsing the first constraint
                while !t.test(TokenType::RParen) {
                    c.push(Type::parse(t)?);
                    if t.consume(TokenType::Comma).is_none() {
                        break;
                    }
                }
                cs.push(Constraint(i, c));
                t.assert(TokenType::RParen)?;

                // now parse the rest of the optional + constraints
                while t.consume(TokenType::Plus).is_some() {
                    let name = t.ident()?;
                    let mut c = vec![];
                    t.assert(TokenType::LParen)?;

                    while !t.test(TokenType::RParen) {
                        c.push(Type::parse(t)?);
                        if t.consume(TokenType::Comma).is_none() {
                            break;
                        }
                    }
                    t.assert(TokenType::RParen)?;
                    cs.push(Constraint(name, c));
                }

                // =>
                t.assert(TokenType::FatArrow)?;

                Ok(QualType(cs, Type::parse(t)?))
            } else {
                // when we check the next char with consume in nl_ignore mode,
                // the token stream can consume as many newlines as it wants
                // and will keep track of if the last token was a newline in
                // nl_last. however, these newlines are *after* the identifer,
                // which we then push back on the queue if parsing constraints
                // fail. Thus we keep track of nl_last, and push a newline as
                // well if it is set
                if t.nl_last {
                    t.queue.push_front(Token {
                        ty: TokenType::NL,
                        pos,
                    })
                }
                t.queue.push_front(Token {
                    ty: TokenType::Ident(i),
                    pos,
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
    fn parse(t: &mut TokenStream) -> Result<Self, SrcError> {
        let cont = Self::parse_tuple(t)?;

        if t.consume(TokenType::Arrow).is_some() {
            let end = Self::parse(t)?;

            Ok(Self::Arrow(Box::new(cont), Box::new(end)))
        } else {
            Ok(cont)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Self, SrcError> {
        if t.consume(TokenType::LParen).is_some() {
            if t.consume(TokenType::RParen).is_some() {
                // Not a tuple, an empty type
                return Ok(Self::Unit);
            }

            let mut inner = vec![Self::parse(t)?];

            // Parse comma separated fields
            while t.consume(TokenType::Comma).is_some() {
                inner.push(Self::parse(t)?);
            }

            t.assert(TokenType::RParen)?;

            if inner.len() == 1 {
                Ok(inner.pop().unwrap())
            } else {
                Ok(Self::Tuple(inner))
            }
        } else {
            Ok(Self::parse_list(t)?)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Result<Self, SrcError> {
        if t.consume(TokenType::LBrace).is_some() {
            let inner = Self::parse(t)?;

            t.assert(TokenType::RBrace)?;

            Ok(Self::Generic(
                vec![inner],
                Box::new(Self::Ident("prelude/list".to_string())),
            ))
        } else {
            Self::parse_generic(t)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Result<Self, SrcError> {
        let base = Self::parse_base(t)?;

        if t.consume(TokenType::LArrow).is_some() {
            let mut vars = Vec::new();
            vars.push(Self::parse(t)?);

            while t.consume(TokenType::Comma).is_some() {
                vars.push(Self::parse(t)?);
            }

            t.assert(TokenType::RArrow)?;

            Ok(Self::Generic(vars, Box::new(base)))
        } else {
            Ok(base)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Self, SrcError> {
        let l = match t.next() {
            Some(a) => a,
            None => {
                return Err(SrcError::new(
                    t.file(),
                    t.eof(),
                    t.eof(),
                    "unexpected end of file while parsing type".to_string(),
                ))
            }
        };

        Ok(match l.ty {
            TokenType::Quote => Type::GenVar(t.ident()?),
            TokenType::Ident(mut i) => {
                while t.consume(TokenType::Slash).is_some() {
                    i.push_str("/");
                    i.push_str(&t.ident()?);
                }

                Type::Ident(i)
            }
            TokenType::Bool => Self::Bool,
            TokenType::U8 => Self::U8,
            TokenType::U16 => Self::U16,
            TokenType::U32 => Self::U32,
            TokenType::U64 => Self::U64,
            TokenType::I8 => Self::I8,
            TokenType::I16 => Self::I16,
            TokenType::I32 => Self::I32,
            TokenType::I64 => Self::I64,
            TokenType::Str => Self::Str,
            _ => {
                return Err(SrcError::new(
                    t.file(),
                    l.pos,
                    l.end(),
                    format!("unexptected token while parsing type: '{}'", l.ty.name()),
                ))
            }
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
    pub fn parse(t: &mut TokenStream) -> Result<Self, SrcError> {
        if t.consume(TokenType::LCurly).is_some() {
            let mut es = vec![];

            loop {
                es.push(Self::parse(t)?);
                if t.consume(TokenType::RCurly).is_some() {
                    break;
                }

                // every expression should be followed by a newline if
                // not the curly brace
                t.nl_aware();
                t.assert(TokenType::NL)?;
                t.nl_ignore();
            }

            Ok(Self::List(es))
        } else {
            Self::orexpr(t)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let and = Self::andexpr(t)?;

        if let Some(()) = t.consume(TokenType::Or) {
            let end = Self::orexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/or".into())),
                Box::new(Self::Tuple(vec![and, end])),
            ))
        } else {
            Ok(and)
        }
    }

    fn andexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let bitor = Self::eqexpr(t)?;

        if let Some(()) = t.consume(TokenType::And) {
            let end = Self::andexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/and".into())),
                Box::new(Self::Tuple(vec![bitor, end])),
            ))
        } else {
            Ok(bitor)
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let rel = Self::relexpr(t)?;

        if let Some(()) = t.consume(TokenType::NotEqual) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/neq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::Equal) {
            let end = Self::eqexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/eq".into())),
                Box::new(Self::Tuple(vec![rel, end])),
            ))
        } else {
            Ok(rel)
        }
    }

    fn relexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let conc = Self::addexpr(t)?;

        if let Some(()) = t.consume(TokenType::LArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/lt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::RArrow) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/gt".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::LTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/leq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::GTE) {
            let end = Self::relexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/geq".into())),
                Box::new(Self::Tuple(vec![conc, end])),
            ))
        } else {
            Ok(conc)
        }
    }

    fn addexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let mul = Self::mulexpr(t)?;

        if let Some(()) = t.consume(TokenType::Plus) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/add".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::Sub) {
            let end = Self::addexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/sub".into())),
                Box::new(Self::Tuple(vec![mul, end])),
            ))
        } else {
            Ok(mul)
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let pow = Self::powexpr(t)?;

        if let Some(()) = t.consume(TokenType::Mul) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/mul".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::Div) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/div".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else if let Some(()) = t.consume(TokenType::Mod) {
            let end = Self::mulexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/mod".into())),
                Box::new(Self::Tuple(vec![pow, end])),
            ))
        } else {
            Ok(pow)
        }
    }

    fn powexpr(t: &mut TokenStream) -> Result<Self, SrcError> {
        let unary = Self::unary(t)?;

        if let Some(()) = t.consume(TokenType::Pow) {
            let end = Self::powexpr(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/pow".into())),
                Box::new(Self::Tuple(vec![unary, end])),
            ))
        } else {
            Ok(unary)
        }
    }

    fn unary(t: &mut TokenStream) -> Result<Self, SrcError> {
        if let Some(()) = t.consume(TokenType::Not) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/not".into())),
                Box::new(un),
            ))
        } else if let Some(()) = t.consume(TokenType::Sub) {
            let un = Self::unary(t)?;
            Ok(Self::Call(
                Box::new(Self::Identifier("prelude/neg".into())),
                Box::new(un),
            ))
        } else {
            Ok(Self::postfix(t)?)
        }
    }

    fn postfix(t: &mut TokenStream) -> Result<Self, SrcError> {
        let primary = Self::primary(t)?;
        Self::postfix_post(t, primary)
    }

    fn postfix_post(t: &mut TokenStream, primary: Expression) -> Result<Self, SrcError> {
        t.nl_aware();

        let pfix = if t.consume(TokenType::LParen).is_some() {
            t.nl_ignore();
            // parse a call with a tuple
            let tup = if let Some(()) = t.consume(TokenType::RParen) {
                Self::Unit
            } else {
                let mut es = Vec::new();
                let e = Self::parse(t)?;
                es.push(e);

                while t.consume(TokenType::Comma).is_some() {
                    es.push(Self::parse(t)?);
                }

                t.assert(TokenType::RParen)?;

                if es.len() == 1 {
                    es.into_iter().next().unwrap()
                } else {
                    Self::Tuple(es)
                }
            };

            Self::Call(Box::new(primary), Box::new(tup))
        } else {
            t.nl_ignore();
            if t.consume(TokenType::Concat).is_some() {
                // parse a concat expression
                let end = Self::parse(t)?;
                Self::Call(
                    Box::new(Self::Identifier("prelude/list.Cons".into())),
                    Box::new(Self::Tuple(vec![primary, end])),
                )
            } else if t.consume(TokenType::Dot).is_some() {
                let func = Expression::Identifier(t.ident()?);

                let mut es = vec![];
                t.assert(TokenType::LParen)?;

                while !t.test(TokenType::RParen) {
                    es.push(Expression::parse(t)?);
                    if t.consume(TokenType::Comma).is_none() {
                        break;
                    }
                }
                t.assert(TokenType::RParen)?;

                let args = match es.len() {
                    0 => primary,
                    _ => {
                        es.insert(0, primary);
                        Expression::Tuple(es)
                    }
                };

                Expression::Call(Box::new(func), Box::new(args))
            } else if t.consume(TokenType::Arrow).is_some() {
                // parse lambda expression
                let pat = primary.to_lambda_pattern()?;
                let end = Self::parse(t)?;

                Self::Lambda(pat, Box::new(end))
            } else {
                return Ok(primary);
            }
        };

        Self::postfix_post(t, pfix)
    }

    fn primary(t: &mut TokenStream) -> Result<Self, SrcError> {
        let l = match t.next() {
            Some(t) => t,
            None => {
                return Err(SrcError::new(
                    t.file(),
                    t.eof(),
                    t.eof(),
                    "unexpected end of file while parsing type".to_string(),
                ))
            }
        };

        match l.ty {
            TokenType::True => Ok(Expression::True),
            TokenType::False => Ok(Expression::False),
            // Let statement
            TokenType::Let => {
                let pat = Pattern::parse(t)?;

                t.assert(TokenType::Assign)?;

                let e = Self::parse(t)?;

                t.assert(TokenType::In)?;

                let body = Self::parse(t)?;

                Ok(Self::Let(pat, Box::new(e), Box::new(body)))
            }
            // If statement
            TokenType::If => {
                let cond = Self::parse(t)?;

                t.assert(TokenType::Then)?;

                let then = Self::parse(t)?;

                t.assert(TokenType::Else)?;

                let else_ = Self::parse(t)?;

                Ok(Self::If(Box::new(cond), Box::new(then), Box::new(else_)))
            }
            // Match statement
            TokenType::Match => {
                let match_ = Self::parse(t)?;

                t.assert(TokenType::With)?;
                t.assert(TokenType::LBrace)?;

                let pat = Pattern::parse(t)?;
                t.assert(TokenType::Arrow)?;
                let e = Self::parse(t)?;

                let mut cases = vec![(pat, e)];

                while t.consume(TokenType::Comma).is_some() {
                    let pat = Pattern::parse(t)?;
                    t.assert(TokenType::Arrow)?;
                    let e = Self::parse(t)?;
                    cases.push((pat, e));
                }

                t.assert(TokenType::RBrace)?;

                Ok(Self::Match(Box::new(match_), cases))
            }
            // String literal
            TokenType::String(s) => Ok(Self::String(s)),
            // Number literal
            TokenType::Num(n) => Ok(Self::Num(n)),
            // Identifier
            TokenType::Ident(mut i) => {
                // This is where we handle identifiers.
                // It may be prefixed with a namespace delimited by slashes,
                // then followed by at most one dot followed by an ident.
                // If the ident that follows is capitalized, it is a constructor,
                // else we don't parse it.

                while t.consume(TokenType::Slash).is_some() {
                    i.push_str("/");
                    i.push_str(&t.ident()?);
                }

                if t.consume(TokenType::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                // if the ident is capitalized then this must be a constructor...
                // we might change this later to be part of the naming/resolution step,
                // but for now this is a good approximate
                if i.chars().next().unwrap().is_uppercase() && !t.test(TokenType::LParen) {
                    Ok(Self::Call(
                        Box::new(Self::Identifier(i)),
                        Box::new(Self::Unit),
                    ))
                } else {
                    Ok(Self::Identifier(i))
                }
            }
            // Tuple
            TokenType::LParen => {
                if let Some(()) = t.consume(TokenType::RParen) {
                    Ok(Self::Unit)
                } else {
                    let mut es = Vec::new();
                    let e = Self::parse(t)?;
                    es.push(e);

                    while t.consume(TokenType::Comma).is_some() {
                        es.push(Self::parse(t)?);
                    }

                    t.assert(TokenType::RParen)?;

                    if es.len() == 1 {
                        Ok(es.into_iter().next().unwrap())
                    } else {
                        Ok(Self::Tuple(es))
                    }
                }
            }
            // List
            TokenType::LBrace => {
                let mut es = Vec::new();

                while !t.test(TokenType::RBrace) {
                    es.push(Self::parse(t)?);
                    if t.consume(TokenType::Comma).is_none() {
                        break;
                    }
                }
                t.assert(TokenType::RBrace)?;

                Ok(Self::cons_from_es(&es))
            }
            // otherwise error
            _ => Err(SrcError::new(
                t.file(),
                l.pos,
                l.end(),
                format!(
                    "expected identifer, constant, or expression, found '{}'",
                    l.ty.name()
                ),
            )),
        }
    }

    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Call(
                Box::new(Self::Identifier("prelude/list.Nil".to_string())),
                Box::new(Self::Unit),
            );
        }

        Self::Call(
            Box::new(Self::Identifier("prelude/list.Cons".to_string())),
            Box::new(Self::Tuple(vec![
                es[0].clone(),
                Self::cons_from_es(&es[1..]),
            ])),
        )
    }

    fn to_lambda_pattern(&self) -> Result<Pattern, SrcError> {
        match self {
            Self::Identifier(s) => Ok(Pattern::Var(s.clone(), None)),
            Self::Tuple(es) => {
                let mut out = vec![];

                for e in es {
                    out.push(e.to_lambda_pattern()?);
                }

                Ok(Pattern::Tuple(out, None))
            }
            Self::Unit => Ok(Pattern::Unit(Some(Type::Unit))),
            Self::Call(f, args) => {
                if let Expression::Identifier(s) = &**f {
                    Ok(Pattern::Cons(
                        s.clone(),
                        Box::new(args.to_lambda_pattern()?),
                        None,
                    ))
                } else {
                    panic!("lambda what?")
                }
            }
            _ => panic!("ahh"),
        }
    }
}

impl Pattern {
    pub fn cons_from_es(es: &[Self]) -> Self {
        if es.is_empty() {
            return Self::Cons(
                "prelude/list.Nil".to_string(),
                Box::new(Self::Unit(None)),
                None,
            );
        }

        Self::Cons(
            "prelude/list.Cons".to_string(),
            Box::new(Self::Tuple(
                vec![es[0].clone(), Self::cons_from_es(&es[1..])],
                None,
            )),
            None,
        )
    }

    fn parse(t: &mut TokenStream) -> Result<Pattern, SrcError> {
        let x = Self::parse_base(t)?;

        if t.consume(TokenType::Concat).is_some() {
            let xs = Self::parse(t)?;
            return Ok(Self::Cons(
                "prelude/list.Cons".into(),
                Box::new(Pattern::Tuple(vec![x, xs], None)),
                None,
            ));
        }

        Ok(x)
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Pattern, SrcError> {
        t.assert(TokenType::LParen)?;
        // We are either the unit type or the tuple type

        if let Some(()) = t.consume(TokenType::RParen) {
            return Ok(Pattern::Unit(Some(Type::Unit)));
        }

        let mut pats = Vec::new();
        let pat = Pattern::parse(t)?;
        pats.push(pat);

        while let Some(()) = t.consume(TokenType::Comma) {
            let pat = Pattern::parse(t)?;
            pats.push(pat);
        }

        t.assert(TokenType::RParen)?;

        if pats.len() == 1 {
            Ok(pats.into_iter().next().unwrap())
        } else {
            Ok(Pattern::Tuple(pats, None))
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Pattern, SrcError> {
        if t.test(TokenType::LParen) {
            return Self::parse_tuple(t);
        }

        let l = match t.next() {
            Some(a) => a,
            None => {
                return Err(SrcError::new(
                    t.file(),
                    t.eof(),
                    t.eof(),
                    "unexpected end of file while parsing type".to_string(),
                ))
            }
        };

        match l.ty {
            TokenType::LBrace => {
                t.assert(TokenType::RBrace)?;
                Ok(Pattern::Cons(
                    "prelude/list.Nil".to_string(),
                    Box::new(Self::Unit(Some(Type::Unit))),
                    None,
                ))
            }
            TokenType::Num(n) => Ok(Pattern::Num(n as i64, Some(Type::I32))),
            TokenType::String(s) => Ok(Pattern::String(s, Some(Type::Str))),
            TokenType::True => Ok(Self::True),
            TokenType::False => Ok(Self::False),
            TokenType::Sub => match t.next() {
                Some(Token {
                    ty: TokenType::Num(n),
                    ..
                }) => Ok(Pattern::Num(-(n as i64), None)),
                Some(l) => Err(SrcError::new(
                    t.file(),
                    l.pos,
                    l.end(),
                    format!("expected number after '-', found '{}'", l.ty.name()),
                )),
                None => Err(SrcError::new(
                    t.file(),
                    t.eof(),
                    t.eof(),
                    "unexpected end of file while parsing type".to_string(),
                )),
            },
            TokenType::Ident(mut i) => {
                if i == "_" {
                    return Ok(Pattern::Any(None));
                }

                while t.consume(TokenType::Dot).is_some() {
                    i.push_str(".");
                    i.push_str(&t.ident()?);
                }

                if i.contains(".") {
                    // This is a namespaced constructor
                    let args = if t.test(TokenType::LParen) {
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
                        let args = if t.test(TokenType::LParen) {
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
            _ => Err(SrcError::new(
                t.file(),
                l.pos,
                l.end(),
                format!("unexpected token while parsing pattern '{}'", l.ty.name()),
            )),
        }
    }
}
