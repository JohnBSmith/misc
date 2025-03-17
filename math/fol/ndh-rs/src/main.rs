
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

fn logic_error(line: usize, info: String) -> Error {
    Box::new(ErrorRecord {kind: ErrorKind::Logic, line, info})
}

#[derive(Debug)]
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

impl Token {
    fn is_symbol(&self, b: &str) -> bool {
        match &self.value {
            TokenValue::Symbol(a) => a.as_slice() == b.as_bytes(),
            _ => false
        }
    }
}

/*
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
*/

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
        b"false" => Some(Bstr::from("⊥")),
        b"true" => Some(Bstr::from("⊤")),
        _ => None
    }
}

fn is_utf8_continuation_byte(byte: u8) -> bool {
    (byte & 0b1100_0000) == 0b1000_0000
}

fn scan(s: &[u8]) -> Vec<Token> {
    let mut i = 0;
    let n = s.len();
    let mut acc: Vec<Token> = Vec::new();
    let mut line = 0;
    while i < n {
        if s[i].is_ascii_alphabetic() || s[i] == b'_' {
            let j = i;
            while i < n && (s[i].is_ascii_alphabetic() || matches!(s[i], b'_' | b'\'')) {
                i += 1;
            }
            let value = match is_keyword(&s[j..i]) {
                Some(symbol) => TokenValue::Symbol(symbol),
                None => TokenValue::Identifier(Bstr::from(&s[j..i]))
            };
            acc.push(Token {line, value});
        } else if s[i].is_ascii_digit() {
            let j = i;
            while i < n && s[i].is_ascii_digit() {
                i += 1;
            }
            let value = TokenValue::Number(Bstr::from(&s[j..i]));
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
        } else if s[i] > 127 {
            let j = i; i += 1;
            while i < n && is_utf8_continuation_byte(s[i]) {i += 1;}
            let value = TokenValue::Symbol(Bstr::from(&s[j..i]));
            acc.push(Token {line, value});
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

#[derive(Debug, Clone)]
enum TermValue {
    Var(Bstr),
    Const(Bstr),
    PatVar(Bstr),
    BoundVar(usize),
    App(Rc<[Term]>)
}

#[derive(Clone)]
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
        ("↔".as_bytes(), (20, L, infix("bijn", Prop, Prop))),
        ("⊢".as_bytes(), (10, R, infix("seq",  Prop, Prop)))
    ])
}

struct Prefix {
    ident: &'static str,
    arg_type: Type,
    value_type: Type,
    special: u32
}

impl Prefix {
    fn call(&self, line: usize, mut x: Term) -> Result<Term, Error> {
        ensure_type(&mut x, line, &self.arg_type)?;
        let f = Term {value: TermValue::Const(Bstr::from(self.ident)), ty: Type::None};
        let value = if self.special != 0 {
            let verum = Term {value: TermValue::Const(Bstr::from("true")), ty: Prop};
            TermValue::App(Rc::from([f, verum, x]))
        } else {
            TermValue::App(Rc::from([f, x]))
        };
        Ok(Term {value, ty: self.value_type.clone()})
    }
}

fn prefix(ident: &'static str, arg_type: Type, value_type: Type) -> Prefix {
    Prefix {ident, arg_type, value_type, special: 0}
}

fn prefix_seq() -> Prefix {
    Prefix {ident: "seq", arg_type: Prop, value_type: Prop, special: 1}
}

fn init_prefix_table() -> HashMap<&'static [u8], (u32, Prefix)> {
    HashMap::from([
        ("⋂".as_bytes(), (100, prefix("Intersection", Ind, Ind))),
        ("⋃".as_bytes(), (100, prefix("Union", Ind, Ind))),
        ("~".as_bytes(), ( 60, prefix("neg", Prop, Prop))),
        ("¬".as_bytes(), ( 60, prefix("neg", Prop, Prop))),
        ("□".as_bytes(), ( 60, prefix("nec", Prop, Prop))),
        ("◇".as_bytes(), ( 60, prefix("pos", Prop, Prop))),
        ("⊢".as_bytes(), ( 10, prefix_seq()))
    ])
}

struct Env {
    tokens: Vec<Token>,
    index: Cell<usize>,
    infix_table:  HashMap<&'static [u8], (u32, Assoc, Infix)>,
    prefix_table: HashMap<&'static [u8], (u32, Prefix)>,
    book: HashMap<Bstr, Term>
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
    } else if token.is_symbol("⊥") {
        env.advance();
        Ok(Term {value: TermValue::Const(Bstr::from("false")), ty: Prop})
    } else if token.is_symbol("⊤") {
        env.advance();
        Ok(Term {value: TermValue::Const(Bstr::from("true")), ty: Prop})
    } else if token.is_symbol("(") {
        let line = token.line;
        env.advance();
        let mut x = formula(env, 0)?;
        let token = env.lookup();
        if token.is_symbol(",") {
            env.advance();
            let y = formula(env, 0)?;
            x = infix("pair", Ind, Ind).call(line, x, y)?;
        }
        let token = env.lookup();
        if !token.is_symbol(")") {
            return Err(syntax_error(token.line, format!("expected ')', but got '{:?}'", token.value)));
        }
        env.advance();
        Ok(x)
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

fn rule_app(env: &Env) -> Result<Vec<Bstr>, Error> {
    let mut acc: Vec<Bstr> = Vec::new();
    let token = env.lookup();
    let x = match &token.value {
        TokenValue::Identifier(x) | TokenValue::Number(x) => x,
        _ => return Err(syntax_error(token.line,
            String::from("expected identifier or label")))
    };
    acc.push(x.clone());
    env.advance();
    loop {
        let token = env.lookup();
        match &token.value {
            TokenValue::Identifier(x) | TokenValue::Number(x) => {
                acc.push(x.clone());
                env.advance();
            },
            TokenValue::Symbol(s) if matches!(s.as_slice(), b"." | b",") =>
                break,
            _ => return Err(syntax_error(token.line,String::from("expected identifier or label")))
        }
    }
    Ok(acc)
}

fn ref_context(env: &Env) -> Result<Vec<Bstr>, Error> {
    let mut acc: Vec<Bstr> = Vec::new();
    let token = env.lookup();
    if token.is_symbol("⊢") {
        return Ok(acc);
    }
    loop {
        let token = env.lookup();
        if let TokenValue::Number(x) = &token.value {
            acc.push(x.clone());
            env.advance();
        }
        let token = env.lookup();
        if !token.is_symbol(",") {break;}
        env.advance();
    }
    Ok(acc)
}

#[derive(Debug)]
struct RefSeq(Vec<Bstr>, Term);

fn ref_sequent(env: &Env) -> Result<RefSeq, Error> {
    let ctx = ref_context(env)?;
    let token = env.lookup();
    if token.is_symbol("⊢") {
        let x = formula(env, 0)?; // todo: formula_type_checked
        Ok(RefSeq(ctx, x))
    } else {
        Err(syntax_error(token.line, String::from("expected context")))
    }
}

#[derive(Debug)]
enum Sum<X, Y> {Left(X), Right(Y)}

#[derive(Debug)]
struct Statement {
    line: usize,
    label: Bstr,
    term: Sum<Term, RefSeq>,
    rule: Vec<Bstr>,
    hint: Option<Term>
}

fn parse_statement(env: &Env) -> Result<Statement, Error> {
    let token = env.lookup();
    let (label, line) = match &token.value {
        TokenValue::Identifier(x) | TokenValue::Number(x) =>
            (x.clone(), token.line),
        _ => return Err(syntax_error(token.line, String::from("expected label")))
    };
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, String::from("expected '.'")));
    }
    env.advance();
    let token = env.lookup();
    let term = if token.is_symbol("(") || matches!(token.value, TokenValue::Identifier(_)) {
        Sum::Left(formula(env, 0)?) // todo: formula_type_checked
    } else {
        Sum::Right(ref_sequent(env)?)
    };
    let token = env.lookup();
    if !token.is_symbol(",") {
        return Err(syntax_error(token.line, String::from("expected ','")));
    }
    env.advance();
    let rule = rule_app(env)?;
    let token = env.lookup();
    let hint = if token.is_symbol(",") {
        Some(formula(env, 0)?) // todo: formula_type_checked
    } else {
        None
    };
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, String::from("expected '.'")));
    }
    env.advance();
    Ok (Statement {line, label, term, rule, hint})
}

fn parse(env: &mut Env, cb: fn(&mut Env, Statement) -> Result<(), Error>) -> Result<(), Error> {
    loop {
        let token = env.lookup();
        if matches!(token.value, TokenValue::None) {break;}
        let stmt = parse_statement(env)?;
        cb(env, stmt)?;
    }
    Ok(())
}

fn app<const N: usize>(args: [Term; N], ty: Type) -> Term {
    Term {value: TermValue::App(Rc::new(args)), ty}
}

fn constant(ident: &str, ty: Type) -> Term {
    Term {value: TermValue::Const(Bstr::from(ident)), ty}
}

fn verum() -> Term {
    constant("true", Prop)
}

fn conjunction(a: Term, b: Term) -> Term {
    app([constant("conj", Type::None), a, b], Prop)
}

fn dummy_sequent (a: Term) -> Term {
    app([constant("seq", Type::None), verum(), a], Prop)
}

fn lookup(book: &HashMap<Bstr, Term>, key: Bstr, line: usize) -> Result<&Term, Error> {
    match book.get(&key) {
        Some(value) => Ok(value),
        None => Err(logic_error(line, format!("label '{}' not found", key)))
    }
}

fn get_arg(t: &Term, k: usize) -> &Term {
    match &t.value {
        TermValue::App(a) => &a[k],
        _ => panic!()
    }
}

fn verify(env: &mut Env, stmt: Statement) -> Result<(), Error> {
    println!("{stmt:#?}");
    let Statement {line, label, term, rule, hint: _} = stmt;
    let form = match term {
        Sum::Right(seq) => {
            let ctx = seq.0;
            let a = seq.1;
            env.book.insert(label.clone(), dummy_sequent(a.clone()));
            let mut h = verum();
            for k in ctx {
                let seq_k = lookup(&env.book, k, line)?;
                let form_k = get_arg(seq_k, 2).clone();
                h = conjunction(h, form_k);
            }
            app([constant("seq", Type::None), h, a], Prop)
        },
        Sum::Left(form) => form
    };
    if label.as_slice() != b"0" {
        env.book.insert(label.clone(), form);
    }
    if rule.iter().any(|x| *x == label) {
        return Err(logic_error(line, "cyclic deduction".to_string()));
    }
    if rule[0].as_slice() == b"def" {
        Ok(()) // todo: definition(line, book, form, rule[1:], label)
    } else if rule[0].as_slice() == b"axiom" {
        Ok(())
    } else {
        Ok(()) // todo: modus_ponens(line, book, form, rule, hint)
    }
}

fn main() {
    let argv: Vec<String> = args().collect();
    let infix_table = init_infix_table();
    let prefix_table = init_prefix_table();
    let book = HashMap::new();
    let mut env = Env{tokens: Vec::new(), index: 0.into(), infix_table, prefix_table, book};
    for file in &argv[1..] {
        let s = fs::read(file).unwrap();
        let tokens = scan(&s);
        env.tokens = tokens;
        env.index.set(0);
        parse(&mut env, verify).unwrap();
    }
}
