use std::collections::HashMap;
use std::collections::VecDeque;

use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};

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
pub struct TokenStream(pub VecDeque<Token>, bool, bool);

impl TokenStream {
    pub fn consume_nl(&mut self) {
        while self.0.front().map(|t| &t.ty) == Some(&TokenType::NL) {
            self.2 = true;
            self.0.pop_front();
        }
    }

    pub fn consume(&mut self, t: TokenType) -> Option<()> {
        if self.test(t.clone()) {
            self.assert(t).unwrap();
            self.2 = false;
            Some(())
        } else {
            None
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if !self.1 {
            self.consume_nl();
        }
        self.0.get(0)
    }

    pub fn next(&mut self) -> Option<Token> {
        if !self.1 {
            self.consume_nl();
        }
        let out = self.0.pop_front();
        if out.is_some() {
            self.2 = false;
        }

        out
    }

    pub fn test(&mut self, t: TokenType) -> bool {
        if !self.1 {
            self.consume_nl();
        }
        if let Some(l) = self.0.get(0) {
            l.ty == t
        } else {
            false
        }
    }

    pub fn assert(&mut self, t: TokenType) -> Result<(), String> {
        if !self.1 {
            self.consume_nl();
        }

        if let Some(l) = self.0.pop_front() {
            if l.ty == t {
                self.2 = false;
                Ok(())
            } else {
                Err(format!("Expected '{}', found '{}'", t.name(), l.ty.name()))
            }
        } else {
            Err(format!("Expected '{}', found EOF", t.name()))
        }
    }

    pub fn ident_tok(&mut self) -> Result<(String, (u32, u32)), String> {
        if !self.1 {
            self.consume_nl();
        }

        if let Some(l) = self.0.pop_front() {
            if let Token {
                ty: TokenType::Ident(s),
                pos,
            } = l
            {
                self.2 = false;
                Ok((s, pos))
            } else {
                self.0.push_front(l.clone());
                Err(format!(
                    "Expected identifier, found '{}' {:?}",
                    l.ty.name(),
                    self
                ))
            }
        } else {
            Err(format!("Expected identifier, found EOF"))
        }
    }

    pub fn ident(&mut self) -> Result<String, String> {
        let (s, _) = self.ident_tok()?;
        Ok(s)
    }

    pub fn nl_aware(&mut self) {
        self.1 = true;
        if self.2 {
            self.0.push_front(Token {
                ty: TokenType::NL,
                pos: (0, 0),
            });
            self.2 = false;
        }
    }

    pub fn nl_ignore(&mut self) {
        self.1 = false;
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Token {
    pub ty: TokenType,
    pub pos: (u32, u32),
}

impl Token {
    fn new(t: TokenType, row: u32, col: u32) -> Self {
        Self {
            ty: t,
            pos: (row, col),
        }
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
    pub fn lex(&mut self, input: &str) -> Result<TokenStream, String> {
        let mut tokens = VecDeque::new();
        let mut chars = input.chars().peekable();
        let mut stack = String::new();
        let mut row = 0;
        let mut col = 0;

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
                    '"' => {
                        self.push_token(&mut tokens, &mut stack, row, col);
                        self.in_string = false;
                    }
                    '\\' => {
                        let new_c = match next {
                            Some('a') => char::from_u32(7).unwrap(),
                            Some('b') => char::from_u32(8).unwrap(),
                            Some('f') => char::from_u32(12).unwrap(),
                            Some('n') => '\n',
                            Some('r') => '\r',
                            Some('t') => '\t',
                            Some('v') => char::from_u32(11).unwrap(),
                            Some('\\') => '\\',
                            Some('"') => '"',
                            Some('?') => '?',
                            Some('0') => char::from_u32(0).unwrap(),
                            _ => return Err("Invalid escape sequence".to_string()),
                        };

                        stack.push(new_c);
                        chars.next();
                        col += 1;
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

                    let val = chars.next().ok_or("Expected char literal".to_string())?;
                    col += 1;

                    let (c, n) = if val == '\\' {
                        let escape = chars
                            .next()
                            .ok_or("Expected escape character".to_string())?;
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
                            _ => return Err("Invalid escape sequence".to_string()),
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
                        return Err("ahhh".to_string());
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
            return Err(format!("Unclosed string literal: expected \""));
        }

        self.push_token(&mut tokens, &mut stack, row, col);

        Ok(TokenStream(tokens, false, false))
    }

    fn push_token(
        &mut self,
        tokens: &mut VecDeque<Token>,
        stack: &mut String,
        row: u32,
        mut col: u32,
    ) {
        col -= stack.len() as u32;
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
