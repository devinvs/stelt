use std::collections::HashMap;
use std::collections::HashSet;

use crate::Token;
use crate::lexer::TokenStream;
use crate::lexer::LexemeFeed;
use crate::lexer::Lexeme;
use crate::lexer::Lexer;
use crate::SteltError;
use crate::error::Range;

use crate::parse_tree::{
    ParseTree,
    DataDecl,
    TypeCons,
    Type,
    FunctionDef,
    Expression,
    Pattern,
};

impl ParseTree {
    pub fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let mut me = Self {
            types: HashMap::new(),
            typedefs: HashMap::new(),
            funcs: HashMap::new(),
            defs: HashMap::new(),
            external: HashSet::new()
        };

        loop {
            match t.peek() {
                Some(Lexeme {token: Token::Extern, ..}) => {
                    t.assert(Token::Extern)?;
                    // must be a typedecl
                    t.assert(Token::Type)?;

                    let name = t.ident()?;
                    t.assert(Token::Colon)?;

                    let ty = Type::parse(t)?;
                    me.typedefs.insert(name.clone(), ty);
                    me.external.insert(name);
                }
                Some(Lexeme {token: Token::Type, ..}) => {
                    // Either a typedecl or datadecl
                    let r = t.assert(Token::Type)?;

                    let name = t.ident()?;

                    // generic args for forall type
                    let mut args = Vec::new();
                    if t.consume(Token::LArrow).is_some() {

                        let arg = t.ident()?;
                        args.push(arg);

                        while t.consume(Token::Comma).is_some() {

                            let arg = t.ident()?;
                            args.push(arg);
                        }

                        t.assert(Token::RArrow)?;
                    }

                    match t.next() {
                        Some(Lexeme {token: Token::Assign, ..}) => {
                            let ty = DataDecl::parse(t, name.clone(), args, r)?;
                            me.types.insert(name, ty);
                        }
                        Some(Lexeme {token: Token::Colon, ..}) => {
                            let ty = Type::parse(t)?;
                            let r = r.add(ty.range());
                            me.typedefs.insert(name, Type::ForAll(args, Box::new(ty), r));
                        }
                        Some(a) => {
                            return Err(SteltError {
                                range: Some(a.range),
                                msg: format!("Expected colon or equals, found '{}'", a.token.name())
                            })
                        }
                        None => {
                            return Err(SteltError {
                                range: None,
                                msg: format!("Expected colon or equals, found EOF")
                            })
                        }
                    }
                }
                Some(Lexeme {token: Token::Def, ..}) => {
                    let name = t.ident()?;

                    let expr = Expression::parse(t)?;
                    me.defs.insert(name, expr);
                }
                Some(Lexeme {token: Token::Ident(_), ..}) => {
                    let range = t.range()?;
                    let name = t.ident()?;
                    let func = FunctionDef::parse(t, name, range)?;
                    if let Some(f) = me.funcs.get_mut(&func.name) {
                        f.push(func);
                    } else {
                        me.funcs.insert(func.name.clone(), vec![func]);
                    }
                }
                Some(a) => {
                    return Err(SteltError {
                        range: Some(a.range),
                        msg: format!("Unexpected token in declaration: '{}'", a.token.name())
                    })
                }
                None => break
            }
        }

        Ok(me)
    }
}

impl DataDecl {
    fn parse(t: &mut TokenStream, name: String, args: Vec<String>, mut r: Range) -> Result<Self, SteltError> {
        if t.consume(Token::LCurly).is_some() {
            let mut members = Vec::new();

            if let Some(r2) = t.consume(Token::RCurly) {
                let r = r.add(r2);
                return Ok(Self::Product(name, args, members, r));
            }

            let n = t.ident()?;
            let ty = Type::parse(t)?;
            members.push((n, ty));

            while t.consume(Token::Comma).is_some() {
                let n = t.ident()?;
                let ty = Type::parse(t)?;
                members.push((n, ty));
            }

            let r = r.add(t.assert(Token::RCurly)?);

            Ok(Self::Product(name, args, members, r))
        } else {
            let mut cons = Vec::new();
            let con = TypeCons::parse(t)?;
            r = r.add(con.range);
            cons.push(con);

            while t.consume(Token::Bar).is_some() {
                let con = TypeCons::parse(t)?;
                r = r.add(con.range);
                cons.push(con);
            }

            Ok(Self::Sum(name, args, cons, r))
        }
    }
}

impl TypeCons {
    fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let r = t.range()?;
        let name = t.ident()?;

        let args = if t.test(Token::LParen) {
            Type::parse(t)?
        } else {
            Type::Unit(r)
        };

        let r = r.add(args.range());
        Ok(Self { name, args, range: r })
    }
}

impl FunctionDef {
    fn parse(t: &mut TokenStream, name: String, r: Range) -> Result<Self, SteltError> {
        // Force function def to start with open paren, but don't consume
        if !t.test(Token::LParen) {
            // Guaranteed to error
            t.assert(Token::LParen)?;
        }

        let args = Pattern::parse(t)?;

        t.assert(Token::Assign)?;

        let body = Expression::parse(t)?;

        let r = r.add(body.range());
        return Ok(FunctionDef {name, args, body, range: r})
    }
}

impl Type {
    pub fn from_str(s: &str) -> Result<Self, SteltError> {
        let mut l = Lexer::default();
        let mut tokens = l.lex(s)?;
        Type::parse(&mut tokens)
    }

    fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        let cont = Self::parse_tuple(t)?;

        if t.consume(Token::Arrow).is_some() {
            let end = Self::parse_tuple(t)?;

            let r = cont.range().add(end.range());
            Ok(Self::Arrow(Box::new(cont), Box::new(end), r))
        } else {
            Ok(cont)
        }
    }

    fn parse_tuple(t: &mut TokenStream) -> Result<Self, SteltError> {
        if let Some(r) = t.consume(Token::LParen) {
            if let Some(r2) = t.consume(Token::RParen) {
                // Not a tuple, an empty type
                return Ok(Self::Unit(r.add(r2)));
            }

            let mut inner = vec![Self::parse(t)?];

            // Parse comma separated fields
            while t.consume(Token::Comma).is_some() {
                inner.push(Self::parse(t)?);
            }

            let r2 = t.assert(Token::RParen)?;

            if inner.len() == 1 {
                Ok(inner.pop().unwrap())
            } else {
                Ok(Self::Tuple(inner, r.add(r2)))
            }
        } else {
            Ok(Self::parse_list(t)?)
        }
    }

    fn parse_list(t: &mut TokenStream) -> Result<Self, SteltError> {
        if let Some(r) = t.consume(Token::LBrace) {
            let inner = Self::parse(t)?;

            let r2 = t.assert(Token::RBrace)?;

            Ok(Self::List(Box::new(inner), r.add(r2)))
        } else {
            Ok(Self::parse_generic(t)?)
        }
    }

    fn parse_generic(t: &mut TokenStream) -> Result<Self, SteltError> {
        let base = Self::parse_base(t)?;

        if t.consume(Token::LArrow).is_some() {
            let mut vars = Vec::new();
            vars.push(Self::parse(t)?);

            while t.consume(Token::Comma).is_some() {
                vars.push(Self::parse(t)?);
            }

            let r2 = t.assert(Token::RArrow)?;
            
            let r = base.range().add(r2);
            Ok(Self::Generic(vars, Box::new(base), r))
        } else if let Some(r) = t.consume(Token::Question) {
            let r2 = r.add(base.range());
            Ok(Self::Generic(
                vec![base],
                Box::new(Self::Ident("Maybe".into(), r)),
                r2
            ))
        } else {
            Ok(base)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Self, SteltError> {
        Ok(match t.next() {
            Some(Lexeme {token: Token::Ident(i), range, ..}) => Self::Ident(i, range),
            Some(Lexeme {token: Token::U8, range, ..}) => Self::U8(range),
            Some(Lexeme {token: Token::U16, range, ..}) => Self::U16(range),
            Some(Lexeme {token: Token::U32, range, ..}) => Self::U32(range),
            Some(Lexeme {token: Token::U64, range, ..}) => Self::U64(range),
            Some(Lexeme {token: Token::I8, range, ..}) => Self::I8(range),
            Some(Lexeme {token: Token::I16, range, ..}) => Self::I16(range),
            Some(Lexeme {token: Token::I32, range, ..}) => Self::I32(range),
            Some(Lexeme {token: Token::I64, range, ..}) => Self::I64(range),
            Some(Lexeme {token: Token::Str, range, ..}) => Self::Str(range),
            Some(a) => {
                return Err(SteltError {
                    range: Some(a.range),
                    msg: format!("Unexpected token in type: '{}'", a.token.name())
                })
            }
            None => {
                return Err(SteltError {
                    range: None,
                    msg: format!("Unexpected EOF in type")
                })
            }
        })
    }
}


impl Expression {
    pub fn parse_list_scoped(t: &mut TokenStream) -> Result<Vec<Expression>, SteltError> {
        let mut exprs = vec![];
        while !t.test(Token::RCurly) {
            let e = match Self::parse(t)? {
                Self::Let(pat, val, _, r) => {
                    let rest = Self::parse_list_scoped(t)?;
                    let body = match rest.len() {
                        0 => Expression::Unit(r),
                        1 => rest.into_iter().next().unwrap(),
                        _ => {
                            let mut r = rest[0].range();
                            r = rest.iter().fold(r, |r1, e| r1.add(e.range()));
                            Self::ExprList(rest, r)
                        }
                    };

                    Self::Let(pat, val, Box::new(body), r)
                }
                a => a
            };

            exprs.push(e);
        }

        Ok(exprs)
    }

    pub fn parse_list(t: &mut TokenStream) -> Result<Self, SteltError> {
        let r = t.assert(Token::LCurly)?;
        let exprs = Self::parse_list_scoped(t)?;
        let r2 = t.assert(Token::RCurly)?;

        match exprs.len() {
            0 => Ok(Expression::Unit(r.add(r2))),
            1 => Ok(exprs.into_iter().next().unwrap()),
            _ => Ok(Self::ExprList(exprs, r.add(r2)))
        }
    }

    pub fn parse(t: &mut TokenStream) -> Result<Self, SteltError> {
        if t.test(Token::LCurly) {
            Self::parse_list(t)
        } else if let Some(r) = t.consume(Token::Let) {
            let pat = Pattern::parse(t)?;

            t.assert(Token::Assign)?;

            let lam = Self::lambda(t)?;

            let r = r.add(lam.range());
            Ok(Self::Let(pat, Box::new(lam), Box::new(Self::Unit(Range::new(0, 0, 0, 0))), r))
        } else if let Some(r) = t.consume(Token::If) {
            let cond = Self::parse(t)?;

            let then = Self::parse_list(t)?;

            t.assert(Token::Else)?;

            let else_ = Self::parse_list(t)?;

            let r = r.add(else_.range());
            Ok(Self::If(Box::new(cond), Box::new(then), Box::new(else_), r))
        } else if let Some(r) = t.consume(Token::Match) {
            let match_ = Self::parse(t)?;

            t.assert(Token::LCurly)?;

            let pat = Pattern::parse(t)?;
            t.assert(Token::Colon)?;
            let e = Self::parse(t)?;

            let mut cases = vec![(pat, e)];

            while t.consume(Token::Comma).is_some() {
                let pat = Pattern::parse(t)?;
                t.assert(Token::Colon)?;
                let e = Self::parse(t)?;
                cases.push((pat, e));
            }

            let r2 =t.assert(Token::RCurly)?;

            Ok(Self::Match(Box::new(match_), cases, r.add(r2)))
        } else {
            Ok(Self::lambda(t)?)
        }
    }

    pub fn lambda(t: &mut TokenStream) -> Result<Self, SteltError> {
        let tup = Self::tuple(t)?;

        if t.consume(Token::Arrow).is_some() {
            let pat = tup.to_lambda_pattern();
            let e = Self::parse(t)?;
            let r = pat.range().add(e.range());
            Ok(Self::Lambda(pat, Box::new(e), r))
        } else {
            Ok(tup)
        }
    }

    pub fn tuple(t: &mut TokenStream) -> Result<Self, SteltError> {
        if let Some(r) = t.consume(Token::LParen) {
            if let Some(r2) = t.consume(Token::RParen) {
                return Ok(Self::Unit(r.add(r2)));
            }

            let mut es = Vec::new();
            let e = Self::parse(t)?;
            es.push(e);


            while t.consume(Token::Comma).is_some() {
                es.push(Self::parse(t)?);
            }

            let r2 = t.assert(Token::RParen)?;

            let e = if es.len() == 1 {
                es.into_iter().next().unwrap()
            } else {
                Self::Tuple(es, r.add(r2))
            };

            // allow postfix expressions on tuples
            Self::postfix_post(t, e)
        } else {
            Self::orexpr(t)
        }
    }

    pub fn orexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let and = Self::andexpr(t)?;

        if let Some(r) = t.consume(Token::Or) {
            let end = Self::orexpr(t)?;
            let r2 = and.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("or".into(), r)),
                Box::new(Self::Tuple(vec![and, end], r2)),
                r2
            ))
        } else {
            Ok(and)
        }
    }

    fn andexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let bitor = Self::bitorexpr(t)?;

        if let Some(r) = t.consume(Token::And) {
            let end = Self::andexpr(t)?;
            let r2 = bitor.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("and".into(), r)),
                Box::new(Self::Tuple(vec![bitor, end], r2)),
                r2
            ))
        } else {
            Ok(bitor)
        }
    }

    fn bitorexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let xor = Self::bitxorexpr(t)?;

        if let Some(r) = t.consume(Token::Bar) {
            let end = Self::bitorexpr(t)?;
            let r2 = xor.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("bitor".into(), r)),
                Box::new(Self::Tuple(vec![xor, end], r2)),
                r2
            ))
        } else {
            Ok(xor)
        }
    }

    fn bitxorexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let and = Self::bitandexpr(t)?;

        if let Some(r) = t.consume(Token::BitXor) {
            let end = Self::bitxorexpr(t)?;
            let r2 = and.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("bitxor".into(), r)),
                Box::new(Self::Tuple(vec![and, end], r2)),
                r2
            ))
        } else {
            Ok(and)
        }
    }

    fn bitandexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let eq = Self::eqexpr(t)?;

        if let Some(r) = t.consume(Token::BitAnd) {
            let end = Self::bitandexpr(t)?;
            let r2 = eq.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("bitand".into(), r)),
                Box::new(Self::Tuple(vec![eq, end], r2)),
                r2
            ))
        } else {
            Ok(eq)
        }
    }

    fn eqexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let rel = Self::relexpr(t)?;

        if let Some(r) = t.consume(Token::NotEqual) {
            let end = Self::eqexpr(t)?;
            let r2 = rel.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("neq".into(), r)),
                Box::new(Self::Tuple(vec![rel, end], r2)),
                r2
            ))
        } else if let Some(r) = t.consume(Token::Equal) {
            let end = Self::eqexpr(t)?;
            let r2 = rel.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("eq".into(), r)),
                Box::new(Self::Tuple(vec![rel, end], r2)),
                r2
            ))
        } else {
            Ok(rel)
        }
    }

    fn relexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let conc = Self::concexpr(t)?;

        if let Some(r) = t.consume(Token::LArrow) {
            let end = Self::relexpr(t)?;
            let r2 = conc.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("lt".into(), r)),
                Box::new(Self::Tuple(vec![conc, end], r2)),
                r2
            ))
        }
        else if let Some(r) = t.consume(Token::RArrow) {
            let end = Self::relexpr(t)?;
            let r2 = conc.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("gt".into(), r)),
                Box::new(Self::Tuple(vec![conc, end], r2)),
                r2
            ))
        }
        else if let Some(r) = t.consume(Token::LTE) {
            let end = Self::relexpr(t)?;
            let r2 = conc.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("leq".into(), r)),
                Box::new(Self::Tuple(vec![conc, end], r2)),
                r2
            ))
        }
        else if let Some(r) = t.consume(Token::GTE) {
            let end = Self::relexpr(t)?;
            let r2 = conc.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("geq".into(), r)),
                Box::new(Self::Tuple(vec![conc, end], r2)),
                r2
            ))
        }
        else {
            Ok(conc)
        }
    }

    fn concexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let add = Self::addexpr(t)?;

        if let Some(r) = t.consume(Token::Concat) {
            let end = Self::concexpr(t)?;
            let r2 = add.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("Cons".into(), r)),
                Box::new(Self::Tuple(vec![add, end], r2)),
                r2
            ))
        } else {
            Ok(add)
        }
    }

    fn addexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let mul = Self::mulexpr(t)?;

        if let Some(r) = t.consume(Token::Plus) {
            let end = Self::addexpr(t)?;
            let r2 = mul.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("add".into(), r)),
                Box::new(Self::Tuple(vec![mul, end], r2)),
                r2
            ))
        } else if let Some(r) = t.consume(Token::Sub) {
            let end = Self::addexpr(t)?;
            let r2 = mul.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("sub".into(), r)),
                Box::new(Self::Tuple(vec![mul, end], r2)),
                r2
            ))
        } else {
            Ok(mul)
        }
    }

    fn mulexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let pow = Self::powexpr(t)?;

        if let Some(r) = t.consume(Token::Mul) {
            let end = Self::mulexpr(t)?;
            let r2 = pow.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("mul".into(), r)),
                Box::new(Self::Tuple(vec![pow, end], r2)),
                r2
            ))
        } else if let Some(r) = t.consume(Token::Div) {
            let end = Self::mulexpr(t)?;
            let r2 = pow.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("div".into(), r)),
                Box::new(Self::Tuple(vec![pow, end], r2)),
                r2
            ))
        } else if let Some(r) = t.consume(Token::Mod) {
            let end = Self::mulexpr(t)?;
            let r2 = pow.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("mod".into(), r)),
                Box::new(Self::Tuple(vec![pow, end], r2)),
                r2
            ))
        } else {
            Ok(pow)
        }
    }

    fn powexpr(t: &mut TokenStream) -> Result<Self, SteltError> {
        let unary = Self::unary(t)?;

        if let Some(r) = t.consume(Token::Pow) {
            let end = Self::powexpr(t)?;
            let r2 = unary.range().add(end.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("pow".into(), r)),
                Box::new(Self::Tuple(vec![unary, end], r2)),
                r2
            ))
        } else {
            Ok(unary)
        }
    }

    fn unary(t: &mut TokenStream) -> Result<Self, SteltError> {
        if let Some(r) = t.consume(Token::Not) {
            let un = Self::unary(t)?;
            let r = r.add(un.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("not".into(), r)),
                Box::new(un),
                r
            ))
        } else if let Some(r) = t.consume(Token::BitNot) {
            let un = Self::unary(t)?;
            let r = r.add(un.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("bitnot".into(), r)),
                Box::new(un),
                r
            ))
        } else if let Some(r) = t.consume(Token::Sub) {
            let un = Self::unary(t)?;
            let r = r.add(un.range());
            Ok(Self::Call(
                Box::new(Self::Identifier("neg".into(), r)),
                Box::new(un),
                r
            ))
        } else {
            Ok(Self::postfix(t)?)
        }
    }

    fn postfix(t: &mut TokenStream) -> Result<Self, SteltError> {
        let primary = Self::primary(t)?;
        let primary = if let Self::Identifier(i, r) = primary {
            let i = match i.as_str() {
                "None" => "Maybe.None",
                "Some" => "Maybe.Some",
                a => a,
            }.to_string();

            Self::Identifier(i, r)
        } else {
            primary
        };
        Self::postfix_post(t, primary)
    }

    fn postfix_post(t: &mut TokenStream, primary: Expression) -> Result<Self, SteltError> {
        if t.test(Token::LParen) {
            let t = Self::tuple(t)?;
            let r = primary.range().add(t.range());
            Ok(Self::Call(Box::new(primary), Box::new(t), r))
        } else if t.consume(Token::Dot).is_some() {
            // Struct membership
            // must be followed by an identifier, which can then be followed
            // by other postfix posts

            let r = t.range()?.add(primary.range());
            let i = t.ident()?;

            let e = Self::Member(Box::new(primary), i, r);
            Self::postfix_post(t, e)
        } else if t.consume(Token::Question).is_some() {
            let then = Expression::parse(t)?;

            t.assert(Token::Colon)?;

            let else_ = Expression::parse(t)?;

            let r = primary.range().add(else_.range());
            Ok(Self::If(Box::new(primary), Box::new(then), Box::new(else_), r))
        } else if t.consume(Token::FatArrow).is_some() {
            // Fancy call with primary as first arg.

            // must be followed by an identifer and then some args
            let f = t.ident()?;
            let primr = primary.range();

            // Get args in tuple
            let mut args = vec![primary];

            let mut r2 = t.assert(Token::LParen)?;
            if let Some(r3) = t.consume(Token::RParen) {
                r2 = r2.add(r3);
            } else {
                args.push(Self::parse(t)?);
                while t.consume(Token::Comma).is_some() {
                    args.push(Self::parse(t)?);
                }
                let r3 = t.assert(Token::RParen)?;
                r2 = r2.add(r3);
            }

            let args = Self::Tuple(args, r2);
            let r = primr.add(args.range());

            let e = Self::Call(
                Box::new(Self::Identifier(f, r)),
                Box::new(args),
                r
            );

            Self::postfix_post(t, e)
        } else {
            Ok(primary)
        }

    }

    fn primary(t: &mut TokenStream) -> Result<Self, SteltError> {
        match t.next() {
            Some(Lexeme {token: Token::String(s), range, ..}) => {
                Ok(Self::Str(s, range))
            }
            Some(Lexeme {token: Token::Num(n), range, ..}) => {
                Ok(Self::Num(n, range))
            }
            Some(Lexeme {token: Token::Ident(i), range, ..}) => {
                Ok(Self::Identifier(i, range))
            }
            Some(Lexeme {token: Token::LParen, ..}) => {
                let e = Expression::parse(t)?;
                t.assert(Token::RParen)?;
                Ok(e)
            }
            Some(Lexeme { token: Token::LBrace, range, ..}) => {
                if let Some(r) = t.consume(Token::RBrace) {
                    let r = r.add(range);
                    return Ok(Self::Call(
                        Box::new(Self::Identifier("List.Nil".to_string(), r)),
                        Box::new(Self::Unit(r)),
                        r
                    ));
                }

                let mut es = vec![Self::parse(t)?];
                while t.consume(Token::Comma).is_some() {
                    es.push(Self::parse(t)?);
                }
                let r = t.assert(Token::RBrace)?;
                let r = r.add(range);

                Ok(Self::cons_from_es(&es, r))
            }
            Some(a) => {
                //panic!("PrimaryExpr: Expected identifier, constant, or expression, found: {:?}", a);
                Err(SteltError {
                    range: Some(a.range),
                    msg: format!("Expected expression, found '{}'", a.token.name())
                })
            }
            None => {
                Err(SteltError {
                    range: None,
                    msg: "Expected expression".into() })
            }
        }
    }

    fn cons_from_es(es: &[Self], r: Range) -> Self {
        if es.is_empty() {
            return Self::Call(
                Box::new(Self::Identifier("List.Nil".to_string(), r)),
                Box::new(Self::Unit(r)),
                r
            );
        }

        Self::Call(
            Box::new(Self::Identifier("List.Cons".to_string(), r)),
            Box::new(Self::Tuple(vec![es[0].clone(), Self::cons_from_es(&es[1..], r)], r)),
            r
        )
    }

    fn to_lambda_pattern(&self) -> Pattern {
        match self {
            Self::Identifier(s, r) => Pattern::Var(s.clone(), r.clone()),
            Self::Tuple(es, r) => Pattern::Tuple(es.iter().map(|e| e.to_lambda_pattern()).collect(), r.clone()),
            _ => panic!("ahh")
        }
    }
}


impl Pattern {
    fn parse(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        if let Some(mut r) = t.consume(Token::LParen) {
            // We are either the unit type or the tuple type

            if let Some(r2) = t.consume(Token::RParen) {
                return Ok(Pattern::Unit(r.add(r2)));
            }

            let mut pats = Vec::new();
            let pat = Pattern::parse_conc(t)?;
            r = r.add(pat.range());
            pats.push(pat);

            while let Some(r2) = t.consume(Token::Comma) {
                r = r.add(r2);
                let pat = Pattern::parse_conc(t)?;
                r = r.add(pat.range());
                pats.push(pat);
            }

            r = r.add(t.assert(Token::RParen)?);

            if pats.len() == 1 {
                Ok(pats.into_iter().next().unwrap())
            } else {
                Ok(Pattern::Tuple(pats, r))
            }
        } else {
            Pattern::parse_conc(t)
        }
    }

    fn parse_conc(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        let a = Self::parse_base(t)?;

        if t.consume(Token::Concat).is_some() {
            let b = Self::parse_base(t)?;
            let r = a.range().add(b.range());

            Ok(Self::Cons(
                "List.Cons".into(),
                Box::new(Pattern::Tuple(vec![a, b], r)),
                r
            ))
        } else {
            Ok(a)
        }
    }

    fn parse_base(t: &mut TokenStream) -> Result<Pattern, SteltError> {
        match t.next() {
            Some(Lexeme {token: Token::LBrace, range, ..}) => {
                let r = t.assert(Token::RBrace)?;
                let r = range.add(r);
                Ok(Pattern::Cons(
                    "List.Nil".to_string(),
                    Box::new(Self::Unit(r)),
                    r
                ))
            }
            Some(Lexeme {token: Token::Num(n), range, ..}) => {
                Ok(Pattern::Num(n, range))
            }
            Some(Lexeme {token: Token::String(s), range, ..}) => {
                Ok(Pattern::Str(s, range))
            }
            Some(Lexeme {token: Token::Ident(i), range, ..}) => {
                // either variable or constructor...
                if t.consume(Token::Dot).is_some() {
                    let range = range.add(t.range()?);
                    let var = t.ident()?;

                    let args = if t.test(Token::LParen) {
                        Pattern::parse(t)?
                    } else {
                        Pattern::Unit(range)
                    };

                    let range = range.add(args.range());
                    Ok(Pattern::Cons(format!("{i}.{var}"), Box::new(args), range))

                } else if t.test(Token::LParen) {
                    let args = Self::parse(t)?;
                    let r = range.add(args.range());

                    Ok(Pattern::Cons(i, Box::new(args), r))
                } else if i=="None" {
                    Ok(Pattern::Cons(
                        "Maybe.None".to_string(),
                        Box::new(Self::Unit(range)),
                        range
                    ))
                } else if i=="Some" {
                    let args = Pattern::parse(t)?;
                    let range = range.add(args.range());

                    Ok(Pattern::Cons(
                        "Maybe.Some".to_string(),
                        Box::new(args),
                        range
                    ))
                } else {
                    Ok(Pattern::Var(i, range))
                }
            }
            _ => panic!("unexpected token")
        }
    }
}
