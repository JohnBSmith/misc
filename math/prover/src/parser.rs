
use std::rc::Rc;

#[derive(Debug)]
pub struct SyntaxError {line: usize, col: usize, text: String}

fn syntax_error(line: usize, col: usize, text: String) -> SyntaxError {
    SyntaxError {line, col, text}
}

impl std::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Syntax error (line {}, col {}): {}",
            self.line + 1, self.col + 1, self.text)
    }
}

#[derive(Clone, Debug)]
enum Symbol {
    None, ParenLeft, ParenRight, Identifier(String),
    Not, And, Or, Implies, Iff, False, True
}

#[derive(Debug)]
struct Token {
    value: Symbol,
    line: usize,
    col: usize
}

static KEYWORDS: &[(&str, Symbol)] = &[
    ("and", Symbol::And),
    ("false", Symbol::False),
    ("iff", Symbol::Iff),
    ("not", Symbol::Not),
    ("or", Symbol::Or),
    ("true", Symbol::True),
];

fn is_keyword(s: &str) -> Option<&Symbol> {
    for (k, v) in KEYWORDS {
        if *k == s {return Some(v);}
    }
    None
}

fn scan(a: &[u8]) -> Result<Vec<Token>, SyntaxError> {
    let mut tokens: Vec<Token> = Vec::new();
    let mut i = 0;
    let mut line = 0;
    let mut col = 0;
    loop {
        let Some(&c) = a.get(i) else {break};
        if c.is_ascii_alphabetic() {
            let col0 = col;
            let mut id = String::new();
            id.push(char::from(c));
            i += 1; col += 1;
            while let Some(&c) = a.get(i) {
                if c.is_ascii_alphabetic() || c.is_ascii_digit() {
                    id.push(char::from(c));
                    i += 1; col += 1;
                } else {
                    break;
                }
            }
            let value = match is_keyword(&id) {
                Some(symbol) => symbol.clone(),
                None => Symbol::Identifier(id)
            };
            tokens.push(Token {value, line, col: col0});
        } else {
            match c {
                b'(' => {
                    tokens.push(Token {value: Symbol::ParenLeft, line, col});
                    i += 1; col += 1;
                },
                b')' => {
                    tokens.push(Token {value: Symbol::ParenRight, line, col});
                    i += 1; col += 1;
                },
                b' ' | b'\t' => {
                    i += 1; col += 1;
                },
                b'\n' => {
                    i += 1; col = 0; line += 1;
                },
                b'~' => {
                    tokens.push(Token {value: Symbol::Not, line, col});
                    i += 1; col += 1;
                },
                b'&' => {
                    tokens.push(Token {value: Symbol::And, line, col});
                    i += 1; col += 1;
                },
                b'|' => {
                    tokens.push(Token {value: Symbol::Or, line, col});
                    i += 1; col += 1;
                },
                b'=' if a.get(i + 1) == Some(&b'>') => {
                    tokens.push(Token {value: Symbol::Implies, line, col});
                    i += 2; col += 2;
                },
                b'-' if a.get(i + 1) == Some(&b'>') => {
                    tokens.push(Token {value: Symbol::Implies, line, col});
                    i += 2; col += 2;
                },
                b'<' if a.get(i + 1) == Some(&b'=') && a.get(i + 2) == Some(&b'>') => {
                    tokens.push(Token {value: Symbol::Iff, line, col});
                    i += 3; col += 3;
                },
                b'<' if a.get(i + 1) == Some(&b'-') && a.get(i + 2) == Some(&b'>') => {
                    tokens.push(Token {value: Symbol::Iff, line, col});
                    i += 3; col += 3;
                },
                c => {
                    return Err(syntax_error(line, col,
                        format!("unexpected character: '{}'.", char::from(c))));
                }
            }
        }
    }
    tokens.push(Token {value: Symbol::None, line, col});
    Ok(tokens)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Prop {
    Variable(Rc<str>),
    Not(Rc<Prop>),
    And(Rc<(Prop, Prop)>),
    Or(Rc<(Prop, Prop)>),
    Implies(Rc<(Prop, Prop)>),
    Iff(Rc<(Prop, Prop)>),
    False,
    True
}

type SyntaxResult = Result<(Prop, usize), SyntaxError>;

const PREC_IFF: u32 = 1;
const PREC_IMPLIES: u32 = 2;
const PREC_OR: u32 = 3;
const PREC_AND: u32 = 4;
const PREC_NOT: u32 = 5;
const PREC_ATOM: u32 = 6;

fn fmt_ast(t: &Prop, parent_prec: u32) -> String {
    let (prec, s) = match t {
        Prop::Variable(id) => (PREC_ATOM, format!("{}", id)),
        Prop::Not(x) => (PREC_NOT, format!("¬{}", fmt_ast(x, PREC_NOT))),
        Prop::And(t) => (PREC_AND, format!("{} ∧ {}",
            fmt_ast(&t.0, PREC_AND), fmt_ast(&t.1, PREC_AND))),
        Prop::Or(t) => (PREC_OR, format!("{} ∨ {}",
            fmt_ast(&t.0, PREC_OR), fmt_ast(&t.1, PREC_OR))),
        Prop::Implies(t) => (PREC_IMPLIES, format!("{} ⇒ {}",
            fmt_ast(&t.0, PREC_IMPLIES), fmt_ast(&t.1, PREC_IMPLIES))),
        Prop::Iff(t) => (PREC_IFF, format!("{} ⇔ {}",
            fmt_ast(&t.0, PREC_IFF), fmt_ast(&t.1, PREC_IFF))),
        Prop::False => return String::from("⊥"),
        Prop::True => return String::from("⊤")
    };
    if prec <= parent_prec {format!("({})", s)} else {s}
}

impl std::fmt::Display for Prop {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", fmt_ast(self, 0))
    }
}

fn atom(a: &[Token], i: usize) -> SyntaxResult {
    match a[i].value {
        Symbol::Identifier(ref x) => Ok((Prop::Variable(Rc::from(x.as_ref())), i + 1)),
        Symbol::False => Ok((Prop::False, i + 1)),
        Symbol::True => Ok((Prop::True, i + 1)),
        Symbol::None => {
            Err(syntax_error(a[i].line, a[i].col,
                String::from("unexpected end of input")))
        },
        Symbol::ParenLeft => {
            let (x, i) = biconditional(a, i + 1)?;
            match a[i].value {
                Symbol::ParenRight => Ok((x, i + 1)),
                _ => Err(syntax_error(a[i].line, a[i].col,
                    String::from("expected ')'")))
            }
        },
        _ => {
            Err(syntax_error(a[i].line, a[i].col,
                String::from("unexpected symbol")))
        }
    }
}

fn negation(a: &[Token], i: usize) -> SyntaxResult {
    if let Symbol::Not = a[i].value {
        let (x, i) = negation(a, i + 1)?;
        Ok((Prop::Not(Rc::new(x)), i))
    } else {
        atom(a, i)
    }
}

fn conjunction(a: &[Token], i: usize) -> SyntaxResult {
    let (mut x, mut i) = negation(a, i)?;
    while let Symbol::And = a[i].value {
        let (y, j) = negation(a, i + 1)?;
        x = Prop::And(Rc::new((x, y)));
        i = j;
    }
    Ok((x, i))
}

fn disjunction(a: &[Token], i: usize) -> SyntaxResult {
    let (mut x, mut i) = conjunction(a, i)?;
    while let Symbol::Or = a[i].value {
        let (y, j) = conjunction(a, i + 1)?;
        x = Prop::Or(Rc::new((x, y)));
        i = j;
    }
    Ok((x, i))
}

fn conditional(a: &[Token], i: usize) -> SyntaxResult {
    let (x, i) = disjunction(a, i)?;
    Ok(if let Symbol::Implies = a[i].value {
        let (y, i) = conditional(a, i + 1)?;
        (Prop::Implies(Rc::new((x, y))), i)
    } else {
        (x, i)
    })
}

fn biconditional(a: &[Token], i: usize) -> SyntaxResult {
    let (x, i) = conditional(a, i)?;
    Ok(if let Symbol::Iff = a[i].value {
        let (y, i) = conditional(a, i + 1)?;
        (Prop::Iff(Rc::new((x, y))), i)
    } else {
        (x, i)
    })
}

pub fn parse(s: &[u8]) -> Result<Prop, SyntaxError> {
    let a = scan(s)?;
    let (x, _) = biconditional(&a, 0)?;
    Ok(x)
}

