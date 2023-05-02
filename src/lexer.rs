use std::collections::HashMap;
use std::iter::Peekable;

use crate::SteltError;

use lazy_static::lazy_static;

lazy_static! {
    pub static ref MAP: HashMap<&'static str, Token> = {
        let mut m = HashMap::new();

        // Keywords
        m.insert("def", Token::Def);
        m.insert("let", Token::Let);
        m.insert("type", Token::Type);
        m.insert("trait", Token::Trait);
        m.insert("impl", Token::Impl);
        m.insert("for", Token::For);
        m.insert("if", Token::If);
        m.insert("else", Token::Else);
        m.insert("match", Token::Match);

        // Built types
        m.insert("u8", Token::U8);
        m.insert("u16", Token::U16);
        m.insert("u32", Token::U32);
        m.insert("u64", Token::U64);
        m.insert("i8", Token::I8);
        m.insert("i16", Token::I16);
        m.insert("i32", Token::I32);
        m.insert("i64", Token::I64);
        m.insert("str", Token::Str);

        // Operators
        m.insert("+", Token::Plus);
        m.insert("-", Token::Sub);
        m.insert("*", Token::Mul);
        m.insert("/", Token::Div);
        m.insert("%", Token::Mod);
        m.insert("**", Token::Pow);
        m.insert("=", Token::Assign);
        m.insert("==", Token::Equal);
        m.insert("!=", Token::NotEqual);
        m.insert("->", Token::Arrow);
        m.insert("::", Token::Concat);
        m.insert("|", Token::Bar);
        m.insert("||", Token::Or);
        m.insert("&&", Token::And);
        m.insert("&", Token::BitAnd);
        m.insert("!", Token::Not);
        m.insert("~", Token::BitNot);
        m.insert("^", Token::BitXor);
        m.insert(".", Token::Dot);
        m.insert("?", Token::Question);

        // Separators
        m.insert("(", Token::LParen);
        m.insert(")", Token::RParen);
        m.insert("[", Token::LBrace);
        m.insert("]", Token::RBrace);
        m.insert("{", Token::LCurly);
        m.insert("}", Token::RCurly);
        m.insert("<", Token::LArrow);
        m.insert(">", Token::RArrow);
        m.insert(",", Token::Comma);
        m.insert(":", Token::Colon);

        m
    };
}


#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Lexeme {
    pub token: Token,
    pub line: usize,
    pub start: usize,
    pub end: usize
}

impl Lexeme {
    fn test(&self, t: Token) -> bool {
        self.token == t
    }
}

pub type TokenStream = Peekable<std::vec::IntoIter<Lexeme>>;

pub trait LexemeFeed {
    fn test(&mut self, t: Token) -> bool;
    fn assert(&mut self, t: Token) -> Result<(), SteltError>;
    fn ident(&mut self) -> Result<String, SteltError>;

    fn consume(&mut self, t: Token) -> bool {
        if self.test(t.clone()) {
            self.assert(t).unwrap();
            true
        } else {
            false
        }
    }
}

impl LexemeFeed for TokenStream {
    fn test(&mut self, t: Token) -> bool {
        if let Some(l) = self.peek() {
            l.test(t)
        } else {
            false
        }
    }

    fn assert(&mut self, t: Token) -> Result<(), SteltError> {
        if let Some(l) = self.next() {
            if l.test(t.clone()) {
                Ok(())
            } else {
                Err(SteltError {
                    line: l.line, start: l.start, end: l.end,
                    msg: format!("Expected {:?}, found {:?}", t, l.token)
                })
            }
        } else {
            Err(SteltError {
                line: 0, start: 0, end: 0,
                msg: format!("Expected {:?}, found EOF", t)
            })
        }
    }

    fn ident(&mut self) -> Result<String, SteltError> {
        if let Some(l) = self.next() {
            if let Lexeme {
                token: Token::Ident(s),
                ..
            } = l {
                Ok(s)
            } else {
                Err(SteltError {
                    line: l.line, start: l.start, end: l.end,
                    msg: format!("Expected identifier, found {:?}", l.token)
                })
            }
        } else {
            Err(SteltError {
                line: 0, start: 0, end: 0,
                msg: format!("Expected identifier, found EOF")
            })
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    // EOF
    EOF,

    // Keywords
    Def,
    Type,
    Let,
    Trait,
    Impl,
    For,
    If,
    Else,
    Match,

    // Builtin Types
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
    Mod,
    Pow,
    Assign,
    Equal,
    NotEqual,
    Or,
    And,
    BitAnd,
    Not,
    BitNot,
    BitXor,
    LTE,
    GTE,
    Dot,
    Question,

    // Fancy stuff maybe?
    Arrow,
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

    Num(u64),
    Char(char),
    String(String),
    Ident(String),
}

impl Token {
    pub fn isdef(&self) -> bool { self==&Token::Def }
    pub fn istype(&self) -> bool { self==&Token::Type }
    pub fn islet(&self) -> bool { self==&Token::Let }

    pub fn isu8(&self) -> bool { self==&Token::U8 }
    pub fn isu16(&self) -> bool { self==&Token::U16 }
    pub fn isu32(&self) -> bool { self==&Token::U32 }
    pub fn isu64(&self) -> bool { self==&Token::U64 }
    pub fn isi8(&self) -> bool { self==&Token::I8 }
    pub fn isi16(&self) -> bool { self==&Token::I16 }
    pub fn isi32(&self) -> bool { self==&Token::I32 }
    pub fn isi64(&self) -> bool { self==&Token::I64 }

    pub fn isnum(&self) -> bool { if let Token::Num(_) = self { true } else { false } }
    pub fn isident(&self) -> bool { if let Token::Ident(_) = self { true } else { false } }
    pub fn ident(&self) -> &String {
        if let Token::Ident(i) = self {i} else {panic!("NO IDENT??!?!")}
    }
}


#[derive(Default)]
pub struct Lexer {
    in_string: bool,
    in_comment: bool,

    line: usize,
    start: usize,
    end: usize,
}


impl Lexer {
    pub fn lex(&mut self, input: &str) -> Result<TokenStream, SteltError> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();

        let mut stack = String::new();

        while let Some(c) = chars.next() {
            let next = chars.peek();

            // If we are in a single line comment go to end of line
            if self.in_comment {
                if c == '\n' {
                    self.line += 1;
                    self.start = 0;
                    self.end = 0;
                    self.in_comment = false;
                }
                continue;
            }

            // If we are in a string skip all characters until "
            // while also transforming escape sequences
            if self.in_string {
                match c {
                    '"' => {
                        self.end += 1;
                        self.push_token(&mut tokens, &mut stack);
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
                                _ => return Err(SteltError {
                                    line: self.line, start: self.start+1, end: self.start+2,
                                    msg: "Invalid escape sequence".to_string()
                                })
                            };

                            self.end += 2;
                            stack.push(new_c);
                            chars.next();
                    }
                    _ => stack.push(c)
                }
                continue;
            }

            match c {
                // Enter a comment
                '/' if next.is_some() && *next.unwrap()=='/' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.in_comment = true;
                    self.end += 2;
                }
                // Enter a string literal
                '"' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.in_string = true;
                    self.end += 1;
                }
                // Char Literal
                '\'' if stack.is_empty() => {
                    self.push_token(&mut tokens, &mut stack);

                    let val = chars.next().ok_or(SteltError {
                        line: self.line, start: self.start, end: self.start+1,
                        msg: "Expected char literal".to_string()
                    })?;

                    if val == '\\' {
                        let escape = chars.next().ok_or(SteltError {
                            line: self.line, start: self.start, end: self.start+1,
                            msg: "Expected escape character".to_string()
                        })?;
                        let new_c = match escape {
                                'a' => char::from_u32(7).unwrap(),
                                'b' => char::from_u32(8).unwrap(),
                                'f' => char::from_u32(12).unwrap(),
                                'r' => '\r',
                                't' => '\t',
                                'v' => char::from_u32(11).unwrap(),
                                '\\' => '\\',
                                '"' => '"',
                                '?' => '?',
                                '0' => char::from_u32(0).unwrap(),
                                _ => return Err(SteltError {
                                    line: self.line, start: self.start+1, end: self.start+2,
                                    msg: "Invalid escape sequence".to_string()
                                })
                            };
                        tokens.push(Lexeme {
                            token: Token::Char(new_c),
                            line: self.line,
                            start: self.start,
                            end: self.start + 4
                        });
                        self.start += 4;
                        self.end += 4;
                    } else {
                        tokens.push(Lexeme {
                            token: Token::Char(val),
                            line: self.line,
                            start: self.start,
                            end: self.end + 3
                        });
                        self.start += 3;
                        self.end += 3;
                    }

                    if let Some('\'') = chars.next() {} else {
                        return Err(SteltError { line: self.line, start: self.start, end: self.end, msg: "Expected closing ' for string literal".to_string() });
                    }
                }
                // Some fancy double char operators???
                '*' if next.is_some() && *next.unwrap() == '*' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::Pow,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                ':' if next.is_some() && *next.unwrap() == ':' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::Concat,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '-' if next.is_some() && *next.unwrap() == '>' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::Arrow,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '|' if next.is_some() && *next.unwrap() == '|' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::Or,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '&' if next.is_some() && *next.unwrap() == '&' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::And,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '=' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::Equal,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '!' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::NotEqual,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '<' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::LTE,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                '>' if next.is_some() && *next.unwrap() == '=' => {
                    self.push_token(&mut tokens, &mut stack);
                    chars.next().unwrap();
                    tokens.push(Lexeme {
                        token: Token::GTE,
                        line: self.line,
                        start: self.start,
                        end: self.start + 2
                    });
                    self.start += 2;
                    self.end = self.start;
                }
                // Separators
                ',' | '(' | ')' | '[' | ']' | '{' | '}' | ':' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push(Lexeme {
                        token: MAP.get(c.to_string().as_str()).unwrap().clone(),
                        line: self.line,
                        start: self.start,
                        end: self.start + 1
                    });
                    self.start += 1;
                    self.end = self.start;
                }

                // Single char Operators
                '+' | '-' | '*' | '/' | '%' | '<' | '>' | '=' | '|' | '&' | '^' | '!' | '~' | '.' | '?' => {
                    self.push_token(&mut tokens, &mut stack);
                    tokens.push(Lexeme {
                        token: MAP.get(c.to_string().as_str()).unwrap().clone(),
                        line: self.line,
                        start: self.start,
                        end: self.start + 1
                    });
                    self.start += 1;
                    self.end = self.start;
                }
                '\n' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.line += 1;
                    self.start = 0;
                    self.end = 0;
                }
                ' ' | '\t' => {
                    self.push_token(&mut tokens, &mut stack);
                    self.start += 1;
                    self.end = self.start;
                },
                _ => {
                    self.end += 1;
                    stack.push(c);
                }
            }
        }
        self.push_token(&mut tokens, &mut stack);

        Ok(tokens.into_iter().peekable())
    }

    fn push_token(&mut self, tokens: &mut Vec<Lexeme>, stack: &mut String) {
        if !stack.is_empty() {
            if self.in_string {
                tokens.push(Lexeme {
                    token: Token::String(stack.clone()),
                    line: self.line,
                    start: self.start,
                    end: self.end
                });
            } else if let Some(tok) = MAP.get(stack.as_str()) {
                tokens.push(Lexeme {
                    token: tok.clone(),
                    line: self.line,
                    start: self.start,
                    end: self.end
                });
            } else if let Ok(i) = str::parse::<u64>(&stack) {
                tokens.push(Lexeme {
                    token: Token::Num(i),
                    line: self.line,
                    start: self.start,
                    end: self.end
                });
            } else {
                tokens.push(Lexeme {
                    token: Token::Ident(stack.clone()),
                    line: self.line,
                    start: self.start,
                    end: self.end
                });
            }

            self.start = self.end;
            stack.clear();
        }
    }
}

