
#![allow(dead_code)]

use std::env::args;
use std::fs;
use std::rc::Rc;
use std::cell::Cell;
use std::collections::HashMap;

mod bstr;
use bstr::Bstr;

#[derive(Debug)]
enum ErrorKind {Syntax, Logic}

#[derive(Debug)]
struct ErrorRecord {
    kind: ErrorKind,
    line: usize,
    info: String
}

type Error = Box<ErrorRecord>;

fn syntax_error(line: usize, info: String) -> Error {
    Box::new(ErrorRecord {kind: ErrorKind::Syntax, line, info})
}

enum TokenValue {
    Number(Bstr),
    Identifier(Bstr),
    Symbol(Bstr),
    None
}

struct Token {
    line: usize,
    value: TokenValue
}

impl std::fmt::Debug for TokenValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenValue::Number(x) => write!(f, "{}", x),
            TokenValue::Identifier(x) => write!(f, "{}", x),
            TokenValue::Symbol(x) => write!(f, "{}", x),
            TokenValue::None => write!(f, "None")
        }
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Token {line, value} = self;
        write!(f, "{}:{:?}", line, value)
    }
}

fn in_sym2(s: &[u8], i: usize, n: usize) -> Option<Bstr> {
    if i + 1 >= n {return None;}
    match &s[i..i + 2] {
        b"|-" => Some(Bstr::from("⊢")),
        b"->" => Some(Bstr::from("→")),
        b"/\\" => Some(Bstr::from("∧")),
        b"\\/" => Some(Bstr::from("∨")),
        _ => None
    }
}

fn is_keyword(s: &[u8]) -> Option<Bstr> {
    match s {
        b"and" => Some(Bstr::from("∧")),
        b"or"  => Some(Bstr::from("∨")),
        b"not" => Some(Bstr::from("¬")),
        _ => None
    }
}

fn scan(s: &[u8]) -> Vec<Token> {
    let mut i = 0;
    let n = s.len();
    let mut acc: Vec<Token> = Vec::new();
    let mut line = 0;
    while i < n {
        if s[i].is_ascii_alphabetic() {
            let j = i;
            while i < n && s[i].is_ascii_alphabetic() {
                i += 1;
            }
            let value = match is_keyword(&s[j..i]) {
                Some(symbol) => TokenValue::Symbol(symbol),
                None => TokenValue::Identifier(Bstr::from(&s[j..i]))
            };
            acc.push(Token {line, value});
        } else if s[i].is_ascii_whitespace() {
            if s[i] == b'\n' {line += 1;}
            i += 1;
        } else if let Some(x) = in_sym2(s, i, n) {
            let value = TokenValue::Symbol(x);
            acc.push(Token {line, value});
            i += 2;
        } else if s[i] == b'#' {
            while i < n && s[i] != b'\n' {i += 1;}
        } else {
            let value = TokenValue::Symbol(Bstr::from(&s[i..i+1]));
            acc.push(Token {line, value});
            i += 1;
        }
    }
    acc.push(Token {line, value: TokenValue::None});
    acc
}

// The variant Some is for type inference
#[derive(Debug, Clone, PartialEq)]
enum Type {None, Some, Prop, Ind}
use Type::{Prop, Ind};

#[derive(Debug)]
enum TermValue {
    Var(Bstr),
    Const(Bstr),
    PatVar(Bstr),
    BoundVar(usize),
    App(Rc<[Term]>)
}

struct Term {
    value: TermValue,
    ty: Type
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            if let TermValue::App(_) = self.value {
                return write!(f, "{:#?}:{:?}", self.value, self.ty);
            }
        }
        write!(f, "{:?}:{:?}", self.value, self.ty)
    }
}

fn ensure_type(t: &mut Term, line: usize, ty: &Type) -> Result<(), Error> {
    if t.ty == Type::Some {
        t.ty = ty.clone();
    } else if t.ty != *ty {
        return Err(syntax_error(line, format!("expected {t:?} to be of type {ty:?}")));
    }
    Ok(())
}

struct Infix {
    ident: &'static str,
    args_type: Type,
    value_type: Type
}

impl Infix {
    fn call(&self, line: usize, mut x: Term, mut y: Term) -> Result<Term, Error> {
        ensure_type(&mut x, line, &self.args_type)?;
        ensure_type(&mut y, line, &self.args_type)?;
        let f = Term {value: TermValue::Const(Bstr::from(self.ident)), ty: Type::None};
        Ok(Term {value: TermValue::App(Rc::from([f, x, y])), ty: self.value_type.clone()})
    }
}

fn infix(ident: &'static str, args_type: Type, value_type: Type) -> Infix {
    Infix {ident, args_type, value_type}
}

#[derive(PartialEq)]
enum Assoc {Left, Right}

fn init_infix_table() -> HashMap<&'static [u8], (u32, Assoc, Infix)> {
    use Assoc::{Left as L, Right as R};
    HashMap::from([
        ("∘".as_bytes(), (90, L, infix("composition", Ind, Ind))),
        ("*".as_bytes(), (90, L, infix("mul", Ind, Ind))),
        ("×".as_bytes(), (90, L, infix("prod", Ind, Ind))),
        ("∩".as_bytes(), (90, L, infix("intersection", Ind, Ind))),
        ("\\".as_bytes(),(90, L, infix("diff", Ind, Ind))),
        ("+".as_bytes(), (80, L, infix("add", Ind, Ind))),
        ("-".as_bytes(), (80, L, infix("sub", Ind, Ind))),
        ("∪".as_bytes(), (80, L, infix("union", Ind, Ind))),
        ("<".as_bytes(), (70, L, infix("lt", Ind, Prop))),
        ("≤".as_bytes(), (70, L, infix("le", Ind, Prop))),
        ("⊆".as_bytes(), (70, L, infix("subset", Ind, Prop))),
        ("∈".as_bytes(), (70, L, infix("element", Ind, Prop))),
        ("=".as_bytes(), (70, L, infix("eq",   Ind,  Prop))),
        ("∧".as_bytes(), (50, L, infix("conj", Prop, Prop))),
        ("∨".as_bytes(), (40, L, infix("disj", Prop, Prop))),
        ("→".as_bytes(), (30, R, infix("subj", Prop, Prop))),
        ("↔".as_bytes(), (20, L, infix("bij",  Prop, Prop))),
        ("⊢".as_bytes(), (10, R, infix("seq",  Prop, Prop)))
    ])
}

struct Prefix {
    ident: &'static str,
    arg_type: Type,
    value_type: Type
}

impl Prefix {
    fn call(&self, line: usize, mut x: Term) -> Result<Term, Error> {
        ensure_type(&mut x, line, &self.arg_type)?;
        let f = Term {value: TermValue::Const(Bstr::from(self.ident)), ty: Type::None};
        Ok(Term {value: TermValue::App(Rc::from([f, x])), ty: self.value_type.clone()})
    }
}

fn prefix(ident: &'static str, arg_type: Type, value_type: Type) -> Prefix {
    Prefix {ident, arg_type, value_type}
}

fn init_prefix_table() -> HashMap<&'static [u8], (u32, Prefix)> {
    HashMap::from([
        ("⋂".as_bytes(), (100, prefix("Intersection", Ind, Ind))),
        ("⋃".as_bytes(), (100, prefix("Union", Ind, Ind))),
        ("~".as_bytes(), ( 60, prefix("neg", Prop, Prop))),
        ("¬".as_bytes(), ( 60, prefix("neg", Prop, Prop))),
        ("□".as_bytes(), ( 60, prefix("nec", Prop, Prop))),
        ("◇".as_bytes(), ( 60, prefix("pos", Prop, Prop)))
        // "⊢": ( 10, prefix_seq), "|-": (10, prefix_seq)
    ])
}

struct Env {
    tokens: Vec<Token>,
    index: Cell<usize>,
    infix_table:  HashMap<&'static [u8], (u32, Assoc, Infix)>,
    prefix_table: HashMap<&'static [u8], (u32, Prefix)>
}

impl Env {
    fn lookup(&self) -> &Token {
        &self.tokens[self.index.get()]
    }
    fn advance(&self) {
        self.index.set(self.index.get() + 1);
    }
}

fn nud(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    if let TokenValue::Identifier(id) = &token.value {
        env.advance();
        Ok(Term {value: TermValue::Var(id.clone()), ty: Type::Some})
    } else {
        if let TokenValue::Symbol(symbol) = &token.value {
            if let Some((bp, op)) = env.prefix_table.get(symbol.as_slice()) {
                env.advance();
                let x = formula(env, *bp)?;
                return op.call(token.line, x);
            }
        } 
        Err(syntax_error(token.line, String::from("unimplemented")))
    }
}

fn formula(env: &Env, rbp: u32) -> Result<Term, Error> {
    let mut x = nud(env)?;
    loop {
        let token = env.lookup();
        if let TokenValue::None = token.value {break;}
        let TokenValue::Symbol(symbol) = &token.value else {break};
        let Some((lbp, assoc, op)) = env.infix_table.get(symbol.as_slice()) else {break};
        if rbp >= *lbp {break;}
        let next_rbp = if *assoc == Assoc::Left {*lbp} else {*lbp - 1};
        env.advance();
        let y = formula(env, next_rbp)?;
        x = op.call(token.line, x, y)?;
    }
    Ok(x)
}

fn main() {
    let argv: Vec<String> = args().collect();
    for file in &argv[1..] {
        let s = fs::read(file).unwrap();
        let tokens = scan(&s);
        let infix_table = init_infix_table();
        let prefix_table = init_prefix_table();
        let env = Env{tokens, index: 0.into(), infix_table, prefix_table};
        let t = formula(&env, 0).unwrap();
        println!("{t:#?}");
    }
}
