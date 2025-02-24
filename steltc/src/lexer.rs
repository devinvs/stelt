use std::collections::HashMap;
use std::collections::VecDeque;
use std::path::PathBuf;

use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};

use crate::error::SrcError;

lazy_static! {
    pub static ref MAP: HashMap<&'static str, TokenType> = {
        let mut m = HashMap::new();

        // Keywords
        m.insert("import", TokenType::Import);
        m.insert("from", TokenType::From);
        m.insert("as", TokenType::As);
        m.insert("alias", TokenType::Alias);
        m.insert("pub", TokenType::Pub);
        m.insert("extern", TokenType::Extern);
        m.insert("type", TokenType::Type);
        m.insert("typefn", TokenType::Typefn);
        m.insert("impl", TokenType::Impl);
        m.insert("let", TokenType::Let);
        m.insert("in", TokenType::In);
        m.insert("if", TokenType::If);
        m.insert("then", TokenType::Then);
        m.insert("else", TokenType::Else);
        m.insert("match", TokenType::Match);
        m.insert("with", TokenType::With);
        m.insert("where", TokenType::Where);

        m.insert("True", TokenType::True);
        m.insert("False", TokenType::False);

        // Built types
        m.insert("u8", TokenType::U8);
        m.insert("u16", TokenType::U16);
        m.insert("u32", TokenType::U32);
        m.insert("u64", TokenType::U64);
        m.insert("i8", TokenType::I8);
        m.insert("i16", TokenType::I16);
        m.insert("i32", TokenType::I32);
        m.insert("i64", TokenType::I64);
        m.insert("bool", TokenType::Bool);
        m.insert("str", TokenType::Str);

        // Operators
        m.insert("+", TokenType::Plus);
        m.insert("-", TokenType::Sub);
        m.insert("*", TokenType::Mul);
        m.insert("/", TokenType::Slash);
        m.insert("%", TokenType::Mod);
        m.insert("**", TokenType::Pow);
        m.insert("=", TokenType::Assign);
        m.insert("==", TokenType::Equal);
        m.insert("!=", TokenType::NotEqual);
        m.insert("=>", TokenType::FatArrow);
        m.insert("->", TokenType::Arrow);
        m.insert("::", TokenType::Concat);
        m.insert("|", TokenType::Bar);
        m.insert("or", TokenType::Or);
        m.insert("and", TokenType::And);
        m.insert("not", TokenType::Not);
        m.insert(".", TokenType::Dot);

        // Separators
        m.insert("(", TokenType::LParen);
        m.insert(")", TokenType::RParen);
        m.insert("[", TokenType::LBrace);
        m.insert("]", TokenType::RBrace);
        m.insert("{", TokenType::LCurly);
        m.insert("}", TokenType::RCurly);
        m.insert("<", TokenType::LArrow);
        m.insert(">", TokenType::RArrow);
        m.insert(",", TokenType::Comma);
        m.insert(":", TokenType::Colon);
        m.insert("'", TokenType::Quote);

        m
    };
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TokenStream {
    pub queue: VecDeque<Token>,
    nl_aware: bool,
    pub nl_last: bool,
    eof: (u32, u32),
    file: PathBuf,
}

impl TokenStream {
    fn new(
        queue: VecDeque<Token>,
        nl_aware: bool,
        nl_last: bool,
        eof: (u32, u32),
        file: PathBuf,
    ) -> Self {
        Self {
            queue,
            nl_aware,
            nl_last,
            eof,
            file,
        }
    }

    pub fn file(&self) -> PathBuf {
        self.file.clone()
    }

    pub fn eof(&self) -> (u32, u32) {
        self.eof
    }

    pub fn consume_nl(&mut self) {
        while self.queue.front().map(|t| &t.ty) == Some(&TokenType::NL) {
            self.nl_last = true;
            self.queue.pop_front();
        }
    }

    pub fn consume(&mut self, t: TokenType) -> Option<()> {
        if self.test(t.clone()) {
            if t == TokenType::NL {
                self.nl_last = true;
            } else {
                self.nl_last = false;
            }

            self.assert(t).unwrap();

            Some(())
        } else {
            None
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if !self.nl_aware {
            self.consume_nl();
        }
        self.queue.get(0)
    }

    pub fn next(&mut self) -> Option<Token> {
        if !self.nl_aware {
            self.consume_nl();
        }
        let out = self.queue.pop_front();
        if out.is_some() {
            if let Some(Token {
                ty: TokenType::NL, ..
            }) = out
            {
                self.nl_last = true;
            } else {
                self.nl_last = false;
            }
        }

        out
    }

    pub fn test(&mut self, t: TokenType) -> bool {
        if !self.nl_aware {
            self.consume_nl();
        }
        if let Some(l) = self.queue.get(0) {
            l.ty == t
        } else {
            false
        }
    }

    pub fn assert(&mut self, t: TokenType) -> Result<(), SrcError> {
        if !self.nl_aware {
            self.consume_nl();
        }

        if let Some(l) = self.queue.pop_front() {
            if l.ty == t {
                if t == TokenType::NL {
                    self.nl_last = true;
                } else {
                    self.nl_last = false;
                }
                Ok(())
            } else {
                Err(SrcError::new(
                    self.file.clone(),
                    l.pos,
                    l.end(),
                    format!("expected '{}', found '{}'", t.name(), l.ty.name()),
                ))
            }
        } else {
            Err(SrcError::new(
                self.file.clone(),
                self.eof,
                self.eof,
                format!("expected '{}', found end of file", t.name()),
            ))
        }
    }

    pub fn ident_tok(&mut self) -> Result<(String, (u32, u32)), SrcError> {
        if !self.nl_aware {
            self.consume_nl();
        }

        if let Some(l) = self.queue.pop_front() {
            if let Token {
                ty: TokenType::Ident(s),
                pos,
            } = l
            {
                self.nl_last = false;
                Ok((s, pos))
            } else {
                self.queue.push_front(l.clone());
                Err(SrcError::new(
                    self.file.clone(),
                    l.pos,
                    l.end(),
                    format!("expected identifier, found '{}'", l.ty.name()),
                ))
            }
        } else {
            Err(SrcError::new(
                self.file.clone(),
                self.eof,
                self.eof,
                "expected identifier, found end of file".to_string(),
            ))
        }
    }

    pub fn ident(&mut self) -> Result<String, SrcError> {
        let (s, _) = self.ident_tok()?;
        Ok(s)
    }

    pub fn nl_aware(&mut self) {
        self.nl_aware = true;
        if self.nl_last {
            self.queue.push_front(Token {
                ty: TokenType::NL,
                pos: (0, 0),
            });
            self.nl_last = false;
        }
    }

    pub fn nl_ignore(&mut self) {
        self.nl_aware = false;
        self.nl_last = false;
    }

    // there's not much that can checked in the lexer, but here's what is covered here
    // - matching parens, braces, curlies
    // - idents don't have invalid characters
    // - strings don't have invalid escape sequences
    pub fn check(&self, file: &PathBuf) -> bool {
        let mut success = true;

        let mut paren_stack = VecDeque::new();
        let mut brace_stack = VecDeque::new();
        let mut curly_stack = VecDeque::new();

        for Token {
            ty,
            pos: (row, col),
        } in self.queue.iter()
        {
            match ty {
                TokenType::Ident(s) => {
                    // Token rules:
                    // - must start with alphabet or _
                    // - must contain only alphanumeric or _ (also . but thats a sneaky case for the parser)
                    // - can end with ! or ?
                    let mut cs = s.chars();

                    let first = cs.next().unwrap();
                    if first != '_' && !first.is_alphabetic() {
                        success = false;
                        SrcError::new(
                            file.clone(),
                            (*row, *col),
                            (*row, *col),
                            "identifiers must start with an alphabetic character or _".to_string(),
                        )
                        .print();
                    }

                    for (i, c) in s.chars().enumerate() {
                        if c != '_'
                            && c != '.'
                            && !c.is_alphanumeric()
                            && !(i == s.len() - 1 && (c == '!' || c == '?'))
                        {
                            success = false;
                            SrcError::new(
                                file.clone(),
                                (*row, *col + i as u32),
                                (*row, *col + i as u32),
                                "identifiers must only contain alphanumeric characters or _"
                                    .to_string(),
                            )
                            .print();
                        }
                    }
                }
                TokenType::String(s) => {
                    let mut backslash = false;

                    for (i, c) in s.chars().enumerate() {
                        if !backslash && c == '\\' {
                            backslash = true;
                            continue;
                        }

                        // TODO: fix for multiline strings
                        if backslash && !"0nrf\\".contains(c) {
                            success = false;
                            SrcError::new(
                                file.clone(),
                                (*row, *col + i as u32 - 1),
                                (*row, *col + i as u32),
                                "invalid string escape sequence".to_string(),
                            )
                            .print();
                        }

                        backslash = false;
                    }
                }
                TokenType::LParen => {
                    paren_stack.push_front((row, col));
                }
                TokenType::RParen => match paren_stack.pop_front() {
                    Some(_) => {}
                    None => {
                        success = false;
                        SrcError::new(
                            file.clone(),
                            (*row, *col),
                            (*row, *col),
                            "unmatched )".to_string(),
                        )
                        .print();
                    }
                },
                TokenType::LBrace => {
                    brace_stack.push_front((row, col));
                }
                TokenType::RBrace => match brace_stack.pop_front() {
                    Some(_) => {}
                    None => {
                        success = false;
                        SrcError::new(
                            file.clone(),
                            (*row, *col),
                            (*row, *col),
                            "unmatched ]".to_string(),
                        )
                        .print();
                    }
                },
                TokenType::LCurly => {
                    curly_stack.push_front((row, col));
                }
                TokenType::RCurly => match curly_stack.pop_front() {
                    Some(_) => {}
                    None => {
                        success = false;
                        SrcError::new(
                            file.clone(),
                            (*row, *col),
                            (*row, *col),
                            "unmatched }".to_string(),
                        )
                        .print();
                    }
                },
                _ => {}
            }
        }

        while let Some((row, col)) = paren_stack.pop_front() {
            success = false;
            SrcError::new(
                file.clone(),
                (*row, *col),
                (*row, *col),
                "unmatched (".to_string(),
            )
            .print();
        }

        while let Some((row, col)) = brace_stack.pop_front() {
            success = false;
            SrcError::new(
                file.clone(),
                (*row, *col),
                (*row, *col),
                "unmatched [".to_string(),
            )
            .print();
        }

        while let Some((row, col)) = curly_stack.pop_front() {
            success = false;
            SrcError::new(
                file.clone(),
                (*row, *col),
                (*row, *col),
                "unmatched {".to_string(),
            )
            .print();
        }

        success
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Token {
    pub ty: TokenType,
    pub pos: (u32, u32),
}

impl Token {
    pub fn new(t: TokenType, row: u32, col: u32) -> Self {
        Self {
            ty: t,
            pos: (row, col),
        }
    }

    pub fn end(&self) -> (u32, u32) {
        (self.pos.0, self.pos.1 + self.ty.name().len() as u32 - 1)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum TokenType {
    // Keywords
    From,
    As,
    Alias,
    Pub,
    Type,
    Let,
    In,
    Typefn,
    Impl,
    For,
    If,
    Then,
    Else,
    Match,
    With,
    Extern,
    Import,
    Where,

    True,
    False,

    // Builtin Types
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    Str,

    // Operators
    Plus,
    Mul,
    Sub,
    Div,
    Slash,
    Mod,
    Pow,
    Assign,
    Equal,
    NotEqual,
    Or,
    And,
    Not,
    LTE,
    GTE,
    Dot,
    Quote,

    // Fancy stuff maybe?
    Arrow,
    FatArrow,
    Concat,
    Bar,

    // Separators
    LArrow,
    RArrow,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LCurly,
    RCurly,
    Comma,
    Colon,

    NL,

    Num(u64),
    Char(char),
    String(String),
    Ident(String),
}

impl TokenType {
    pub fn name(&self) -> String {
        match self {
            Self::NL => "\\n",
            Self::Quote => "'",
            Self::From => "from",
            Self::As => "as",
            Self::Alias => "alias",
            Self::Pub => "pub",
            Self::True => "True",
            Self::False => "False",
            Self::Bool => "bool",
            Self::Where => "where",
            Self::With => "with",
            Self::Then => "then",
            Self::In => "in",
            Self::Extern => "extern",
            Self::FatArrow => "=>",
            Self::Type => "type",
            Self::Let => "let",
            Self::Typefn => "typefn",
            Self::Impl => "impl",
            Self::For => "for",
            Self::If => "if",
            Self::Else => "else",
            Self::Match => "match",
            Self::Import => "import",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::Str => "str",
            Self::Plus => "+",
            Self::Mul => "*",
            Self::Sub => "-",
            Self::Slash => "/",
            Self::Div => "//",
            Self::Mod => "%",
            Self::Pow => "**",
            Self::Assign => "=",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::Or => "or",
            Self::And => "and",
            Self::Not => "not",
            Self::LTE => "<=",
            Self::GTE => ">=",
            Self::Dot => ".",
            Self::Arrow => "->",
            Self::Concat => "::",
            Self::Bar => "|",
            Self::LArrow => "<",
            Self::RArrow => ">",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "[",
            Self::RBrace => "]",
            Self::LCurly => "{",
            Self::RCurly => "}",
            Self::Comma => ",",
            Self::Colon => ":",
            Self::Num(n) => return n.to_string(),
            Self::Char(c) => return c.to_string(),
            Self::String(s) => s,
            Self::Ident(s) => s,
        }
        .into()
    }
}

#[derive(Default)]
pub struct Lexer {
    in_string: bool,
    in_comment: bool,
}

impl Lexer {
    pub fn lex(&mut self, input: &str, file: &PathBuf) -> Result<TokenStream, TokenStream> {
        let mut tokens = VecDeque::new();
        let mut chars = input.chars().peekable();
        let mut stack = String::new();
        let mut row = 0;
        let mut col = 0;

        let mut fail = false;

        while let Some(c) = chars.next() {
            let next = chars.peek();

            // If we are in a single line comment go to end of line
            if self.in_comment {
                if c == '\n' {
                    self.in_comment = false;
                    tokens.push_back(Token::new(TokenType::NL, row, col));
                    row += 1;
                    col = 0;
                }
                continue;
            }

            // If we are in a string skip all characters until "
            // while also transforming escape sequences
            if self.in_string {
                match c {
                    '"' if stack.chars().last() != Some('\\') => {
                        self.push_token(&mut tokens, &mut stack, row, col);
                        self.in_string = false;
                    }
                    '\n' => {
                        // for now we will allow multiline strings
                        stack.push(c);
                        row += 1;
                        col = 0;
                        continue;
                    }
                    _ => stack.push(c),
                }
                col += 1;
                continue;
            }

            match c {
                // Enter a comment
                '#' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    self.in_comment = true;
                }
                // Enter a string literal
                '"' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    self.in_string = true;
                }
                // Char Literal or type var...
                '\'' if stack.is_empty() => {
                    self.push_token(&mut tokens, &mut stack, row, col);

                    let val = match chars.next() {
                        Some('\n') => {
                            SrcError::new(
                                file.clone(),
                                (row, col),
                                (row, col),
                                "unclosed char literal".to_string(),
                            )
                            .print();
                            row += 1;
                            col = 0;
                            continue;
                        }
                        Some(c) => c,
                        _ => {
                            SrcError::new(
                                file.clone(),
                                (row, col),
                                (row, col),
                                "unexpected end of file".to_string(),
                            )
                            .print();
                            return Err(TokenStream::new(
                                tokens,
                                false,
                                false,
                                (row, col),
                                file.clone(),
                            ));
                        }
                    };

                    col += 1;

                    let (c, n) = if val == '\\' {
                        let escape = match chars.next() {
                            Some('\n') => {
                                SrcError::new(
                                    file.clone(),
                                    (row, col),
                                    (row, col),
                                    "unclosed char literal".to_string(),
                                )
                                .print();
                                row += 1;
                                col = 0;
                                continue;
                            }
                            Some(c) => c,
                            _ => {
                                SrcError::new(
                                    file.clone(),
                                    (row, col),
                                    (row, col),
                                    "unexpected end of file".to_string(),
                                )
                                .print();
                                return Err(TokenStream::new(
                                    tokens,
                                    false,
                                    false,
                                    (row, col),
                                    file.clone(),
                                ));
                            }
                        };

                        let new_c = match escape {
                            'a' => char::from_u32(7).unwrap(),
                            'b' => char::from_u32(8).unwrap(),
                            'f' => char::from_u32(12).unwrap(),
                            'r' => '\r',
                            't' => '\t',
                            'n' => '\n',
                            '\'' => '\'',
                            'v' => char::from_u32(11).unwrap(),
                            '\\' => '\\',
                            '"' => '"',
                            '?' => '?',
                            '0' => char::from_u32(0).unwrap(),
                            '\n' => {
                                SrcError::new(
                                    file.clone(),
                                    (row, col),
                                    (row, col),
                                    "expected escape character, found newline".to_string(),
                                )
                                .print();
                                row += 1;
                                col = 0;
                                continue;
                            }
                            _ => {
                                fail = true;
                                SrcError::new(
                                    file.clone(),
                                    (row, col),
                                    (row, col),
                                    "invalid character escape character".to_string(),
                                )
                                .print();
                                'X' // just a placeholder since lexing fails
                            }
                        };
                        col += 1;
                        (new_c, 3)
                    } else {
                        (val, 2)
                    };

                    if let Some('\'') = chars.peek() {
                        chars.next();
                        tokens.push_back(Token::new(TokenType::Char(c), row, col));
                        col += 1;
                    } else if n == 3 {
                        panic!("ahhh in the lexer");
                    } else {
                        // not a char literal, parse as type var
                        tokens.push_back(Token::new(TokenType::Quote, row, col));
                        stack.push(c);
                    }
                }
                // Some fancy double char operators???
                '*' if next.is_some() && *next.unwrap() == '*' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Pow, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                ':' if next.is_some() && *next.unwrap() == ':' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Concat, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '-' if next.is_some() && *next.unwrap() == '>' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Arrow, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '|' if next.is_some() && *next.unwrap() == '|' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Or, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '&' if next.is_some() && *next.unwrap() == '&' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::And, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '=' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Equal, col, row));
                    chars.next().unwrap();
                    col += 1;
                }
                '!' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::NotEqual, col, row));
                    chars.next().unwrap();
                    col += 1;
                }
                '<' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::LTE, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '>' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::GTE, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '=' if next.is_some() && *next.unwrap() == '>' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::FatArrow, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                '/' if next.is_some() && *next.unwrap() == '/' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::Div, row, col));
                    chars.next().unwrap();
                    col += 1;
                }
                // Separators
                ',' | '(' | ')' | '[' | ']' | '{' | '}' | ':' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(
                        MAP.get(c.to_string().as_str()).unwrap().clone(),
                        row,
                        col,
                    ));
                }

                // Single char Operators
                '+' | '-' | '*' | '/' | '%' | '<' | '>' | '=' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(
                        MAP.get(c.to_string().as_str()).unwrap().clone(),
                        row,
                        col,
                    ));
                }
                '\n' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                    tokens.push_back(Token::new(TokenType::NL, row, col));
                    row += 1;
                    col = 0;
                    continue;
                }
                ' ' | '\t' => {
                    self.push_token(&mut tokens, &mut stack, row, col);
                }
                _ => {
                    stack.push(c);
                }
            }
            col += 1;
        }

        if self.in_string {
            fail = true;
            SrcError::new(
                file.clone(),
                (row, col),
                (row, col),
                "unclosed string literal, expected \"".to_string(),
            )
            .print();
        } else {
            self.push_token(&mut tokens, &mut stack, row, col);
        }

        if fail {
            Err(TokenStream::new(
                tokens,
                false,
                false,
                (row, col),
                file.clone(),
            ))
        } else {
            Ok(TokenStream::new(
                tokens,
                false,
                false,
                (row, col),
                file.clone(),
            ))
        }
    }

    fn push_token(
        &mut self,
        tokens: &mut VecDeque<Token>,
        stack: &mut String,
        row: u32,
        mut col: u32,
    ) {
        col = col.saturating_sub(stack.len() as u32);
        if !stack.is_empty() {
            if self.in_string {
                tokens.push_back(Token::new(TokenType::String(stack.clone()), row, col));
            } else if let Some(tok) = MAP.get(stack.as_str()) {
                tokens.push_back(Token::new(tok.clone(), row, col));
            } else if let Ok(i) = str::parse::<u64>(&stack) {
                tokens.push_back(Token::new(TokenType::Num(i), row, col));
            } else {
                tokens.push_back(Token::new(TokenType::Ident(stack.clone()), row, col));
            }

            stack.clear();
        }
    }
}
