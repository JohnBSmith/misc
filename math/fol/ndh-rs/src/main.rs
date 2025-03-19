
use std::env::args;
use std::fs;
use std::rc::Rc;
use std::cell::Cell;
use std::collections::HashMap;

mod bstr;
use bstr::Bstr;

#[cfg(test)]
mod tests;

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
            while i < n && (s[i].is_ascii_alphabetic() ||
                s[i].is_ascii_digit() ||
                matches!(s[i], b'_' | b'\''))
            {
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
enum Type {None, Some, Prop, Ind, Fn}
use Type::{Prop, Ind};

#[derive(Debug, Clone)]
enum TermValue {
    Var(Bstr),
    Const(Bstr),
    PatVar(Bstr),
    #[allow(dead_code)] BoundVar(usize),
    App(Rc<[Term]>)
}

#[derive(Clone)]
struct Term {
    value: TermValue,
    ty: Type
}

impl Term {
    fn is_connective(&self, ident: &str) -> bool {
        match &self.value {
            App(a) => matches!(&a[0].value,
                Const(x) if x.as_slice() == ident.as_bytes()),
            _ => false
        }
    }

    fn is_const(&self, ident: &str) -> bool {
        matches!(&self.value, Const(x) if x.as_slice() == ident.as_bytes())
    }

    fn arg(&self, k: usize) -> &Self {
        match &self.value {
            App(a) => &a[k],
            _ => panic!()
        }
    }
}

use TermValue::{Var, Const, PatVar, BoundVar, App};

fn term(value: TermValue, ty: Type) -> Term {
    Term {value, ty}
}

fn app<const N: usize>(args: [Term; N], ty: Type) -> Term {
    term(App(Rc::new(args)), ty)
}

fn constant(ident: &str, ty: Type) -> Term {
    term(Const(Bstr::from(ident)), ty)
}

fn verum() -> Term {
    constant("true", Prop)
}

fn conjunction(a: Term, b: Term) -> Term {
    app([constant("conj", Type::None), a, b], Prop)
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            if let App(_) = self.value {
                return write!(f, "{:#?}:{:?}", self.value, self.ty);
            }
        }
        write!(f, "{:?}:{:?}", self.value, self.ty)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            Var(x) | Const(x) | PatVar(x) => write!(f, "{}", x),
            BoundVar(x) => write!(f, "${}", x),
            App(a) => {
                write!(f, "(")?;
                let mut first = true;
                for x in a.as_ref() {
                    if first {first = false} else {write!(f, " ")?;}
                    write!(f, "{}", x)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn ensure_type(t: &mut Term, line: usize, ty: &Type) -> Result<(), Error> {
    if t.ty == Type::Some {
        t.ty = ty.clone();
    } else if t.ty != *ty {
        return Err(syntax_error(line, format!(
            "expected {t:?} to be of type {ty:?}")));
    }
    Ok(())
}

struct Infix {
    ident: &'static str,
    args_type: Type,
    value_type: Type
}

impl Infix {
    fn call(&self, line: usize, mut x: Term, mut y: Term)
    -> Result<Term, Error>
    {
        ensure_type(&mut x, line, &self.args_type)?;
        ensure_type(&mut y, line, &self.args_type)?;
        let f = constant(self.ident, Type::None);
        Ok(app([f, x, y], self.value_type.clone()))
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
        let f = constant(self.ident, Type::None);
        let value = if self.special != 0 {
            App(Rc::from([f, verum(), x]))
        } else {
            App(Rc::from([f, x]))
        };
        Ok(term(value, self.value_type.clone()))
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
    fn new() -> Self {
        Self {
            tokens: Vec::new(),
            index: 0.into(),
            infix_table: init_infix_table(),
            prefix_table: init_prefix_table(),
            book: HashMap::new()
        }
    }
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
        Ok(term(TermValue::Var(id.clone()),Type::Some))
    } else if token.is_symbol("⊥") {
        env.advance();
        Ok(constant("false", Prop))
    } else if token.is_symbol("⊤") {
        env.advance();
        Ok(constant("true", Prop))
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
            return Err(syntax_error(token.line, format!(
                "expected ')', but got '{:?}'", token.value)));
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
        Err(syntax_error(token.line, "unimplemented".to_string()))
    }
}

fn application(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    let line0 = token.line;
    let x = nud(env)?;
    let token = env.lookup();
    if matches!(&token.value, TokenValue::Identifier(_)) ||
       matches!(&token.value, TokenValue::Symbol(s)
           if {let s = s.as_slice(); s == b"(" || s == b"{"})
    {
        let mut args: Vec<Term> = vec![x];
        while matches!(&token.value, TokenValue::Identifier(_)) ||
              matches!(&token.value, TokenValue::Symbol(s)
                  if {let s = s.as_slice(); s == b"(" || s == b"{"})
        {
            let x = nud(env)?;
            args.push(x);
        }
        if !matches!(&args[0].value, Const(_) | Var(_)) {
            return Err(syntax_error(line0,
                "predicate or function must be an identifier".to_string()));
        }
        args[0].ty = Type::Fn;
        Ok(term(App(Rc::from(args)), Type::Some))
    } else {
        Ok(x)
    }
}

fn formula(env: &Env, rbp: u32) -> Result<Term, Error> {
    let mut x = application(env)?;
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

fn formula_type_checked(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    let mut x = formula(env, 0)?;
    ensure_type(&mut x, token.line, &Prop)?;
    Ok(x)
}

fn rule_app(env: &Env) -> Result<Vec<Bstr>, Error> {
    let mut acc: Vec<Bstr> = Vec::new();
    let token = env.lookup();
    let x = match &token.value {
        TokenValue::Identifier(x) | TokenValue::Number(x) => x,
        _ => return Err(syntax_error(token.line,
            "expected identifier or label".to_string()))
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
            _ => return Err(syntax_error(token.line,
                "expected identifier or label".to_string()))
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
        env.advance();
        let x = formula_type_checked(env)?;
        Ok(RefSeq(ctx, x))
    } else {
        Err(syntax_error(token.line, "expected context".to_string()))
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
        _ => return Err(syntax_error(token.line, "expected label".to_string()))
    };
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    let token = env.lookup();
    let term = if token.is_symbol("(") || matches!(token.value, TokenValue::Identifier(_)) {
        Sum::Left(formula_type_checked(env)?)
    } else {
        Sum::Right(ref_sequent(env)?)
    };
    let token = env.lookup();
    if !token.is_symbol(",") {
        return Err(syntax_error(token.line, "expected ','".to_string()));
    }
    env.advance();
    let rule = rule_app(env)?;
    let token = env.lookup();
    let hint = if token.is_symbol(",") {
        Some(formula_type_checked(env)?)
    } else {
        None
    };
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
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

fn dummy_sequent (a: Term) -> Term {
    app([constant("seq", Type::None), verum(), a], Prop)
}

fn lookup<'a, 'b>(book: &'a HashMap<Bstr, Term>, key: &'b Bstr, line: usize)
-> Result<&'a Term, Error>
{
    match book.get(key) {
        Some(value) => Ok(value),
        None => Err(logic_error(line, format!("label '{}' not found", key)))
    }
}

fn pattern_from(t: &Term) -> Term {
    match &t.value {
        Var(x) => term(PatVar(x.clone()), t.ty.clone()),
        App(a) => term(
            App(Rc::from(a.iter().map(pattern_from).collect::<Vec<_>>())),
            t.ty.clone()
        ),
        _ => t.clone()
    }
}

fn term_eq(env: &Env, a: &Term, b: &Term) -> bool {
    if a.ty != b.ty {return false;}
    match (&a.value, &b.value) {
        (Var(a), Var(b)) => a == b,
        (Const(a), Const(b)) => a == b,
        (BoundVar(a), BoundVar(b)) => a == b,
        (App(a), App(b)) => a.as_ref().iter().zip(b.as_ref()).all(
            |(x, y)| term_eq(env, x, y)),
        _ => false
    }
}

mod substi {
    use crate::{Term, Bstr};
    #[derive(Clone)]
    pub struct Subs(Vec<(Bstr, Term)>);
    // There are so few variables in ordinary inference rules
    // that Vec turns out to be more efficient than HashMap.

    impl Subs {
        pub fn new() -> Self {
            Self(Vec::new())
        }
        pub fn set(&mut self, key: Bstr, value: Term) {
            self.0.push((key, value));
        }
        pub fn get(&self, key: &Bstr) -> Option<&Term> {
            for (x, y) in &self.0 {
                if key == x {return Some(y);}
            }
            None
        }
        pub fn set_to(&mut self, subs: Self) {
            self.0.clear();
            self.0.extend(subs.0);
        }
    }

    /*
    #[derive(Clone)]
    struct Subs(HashMap<Bstr, Term>);

    impl Subs {
        fn new() -> Self {
            Self(HashMap::new())
        }
        fn set(&mut self, key: Bstr, value: Term) {
            self.0.insert(key, value);
        }
        fn get(&self, key: &Bstr) -> Option<&Term> {
            self.0.get(key)
        }
        fn set_to(&mut self, subs: Self) {
            self.0.clear();
            self.0.extend(subs.0);
        }
    }
    */
}
use substi::Subs;

fn subs_rec(t: &Term, subs: &Subs) -> Term {
    match &t.value {
        PatVar(x) => {
            match subs.get(x) {
                Some(value) => value.clone(),
                None => t.clone()
            }
        },
        App(a) => term(
            App(Rc::from(a.iter().map(|x|
                subs_rec(x, subs)).collect::<Vec<_>>())),
            t.ty.clone()),
        _ => t.clone()
    }
}

fn conj_list(t: &Term, subs: Option<&Subs>, acc: &mut Vec<Term>) {
    if t.is_const("true") {
    } else if t.is_connective("conj") {
        conj_list(t.arg(1), subs, acc);
        conj_list(t.arg(2), subs, acc);
    } else if let Some(subs) = subs {
        conj_list(&subs_rec(t, subs), None, acc);
    } else {
        acc.push(t.clone());
    }
}

fn set_in(env: &Env, x: &Term, b: &[Term]) -> bool {
    b.iter().any(|y| term_eq(env, x, y))
}

fn subset(env: &Env, a: &[Term], b: &[Term]) -> bool {
    a.iter().all(|x| set_in(env, x, b))
}

fn set_eq(env: &Env, a: &[Term], b: &[Term]) -> bool {
    subset(env, a, b) && subset(env, b, a)
}

fn unify_seq(env: &Env, line: usize, pattern: &[Term], a: &[Term], subs: &mut Subs)
-> Result<bool, Error>
{
    let result = unify(env, line, &a[2], &pattern[2], subs)?;
    if !result {return Ok(false);}
    let mut l1 = Vec::new();
    let mut l2 = Vec::new();
    conj_list(&pattern[1], Some(subs), &mut l2);
    conj_list(&a[1], None, &mut l1);
    Ok(set_eq(env, &l1, &l2))
}

fn unify_args(env: &Env, line: usize, a: &[Term], b: &[Term], subs: &mut Subs)
-> Result<bool, Error>
{
    if a.len() != b.len() {return Ok(false);}
    let mut subs_copy = subs.clone();
    for (pat, x) in a.as_ref().iter().zip(b.as_ref()) {
        let result = unify(env, line, x, pat, subs)?;
        if !result {
            if a[0].is_const("seq") && b[0].is_const("seq") {
                let result = unify_seq(env, line, a, b, &mut subs_copy)?;
                if result {
                    subs.set_to(subs_copy);
                }
                return Ok(result);
            }
            return Ok(false);
        }
    }
    Ok(true)
}

fn unify(env: &Env, line: usize, t: &Term, pattern: &Term, subs: &mut Subs)
-> Result<bool, Error>
{
    if pattern.ty != t.ty {
        return Err(logic_error(line, format!("type error {pattern:?}, {t:?}")));
    }
    // println!("    {:?}\nmit {:?}\n", t, pattern);
    match &pattern.value {
        PatVar(a) => {
            Ok(if let Some(b) = subs.get(a) {
                term_eq(env, b, t)
            } else {
                subs.set(a.clone(), t.clone());
                true
            })
        },
        App(a) => {
            match &t.value {
                App(b) => unify_args(env, line, a, b, subs),
                _ => Ok(false)
            }
        },
        _ => Ok(term_eq(env, pattern, t))
    }
}

fn conclusion(env: &Env, line: usize, b: &Term, c: &Term, subs: &mut Subs, args: &[Bstr])
-> Result<(), Error>
{
    let result = unify(env, line, b, c, subs)?;
    if !result {
        return Err(logic_error(line,
            format!("unification failed for {}, in conclusion", args[0])));
    }
    Ok(())
}

fn modus_ponens(env: &Env, line: usize, b: Term, args: &[Bstr], _hint: Option<Term>)
-> Result<(), Error>
{
    let c0 = pattern_from(lookup(&env.book, &args[0], line)?);
    let mut c = &c0;
    // println!("{c:#?}");

    let mut subs = Subs::new();
    for i in 1..args.len() {
        let a = lookup(&env.book, &args[i], line)?;
        if !c.is_connective("subj") {
            return Err(logic_error(line, "expected a rule/subjunction".to_string()));
        }
        let result = unify(env, line, a, c.arg(1), &mut subs)?;
        if !result {
            // println!("    {}\nmit {}\n", a, get_arg(c, 1));
            return Err(logic_error(line,
                format!("unification failed for {}, argument {}", args[0], i)));
        }
        c = c.arg(2);
    }
    conclusion(env, line, &b, c, &mut subs, args)
}

fn verify_cb(env: &mut Env, stmt: Statement) -> Result<(), Error> {
    let Statement {line, label, term, rule, hint} = stmt;
    let form = match term {
        Sum::Right(seq) => {
            let ctx = seq.0;
            let a = seq.1;
            env.book.insert(label.clone(), dummy_sequent(a.clone()));
            let mut h = verum();
            for k in ctx {
                let seq_k = lookup(&env.book, &k, line)?;
                let form_k = seq_k.arg(2).clone();
                h = conjunction(h, form_k);
            }
            app([constant("seq", Type::None), h, a], Prop)
        },
        Sum::Left(form) => form
    };
    if label.as_slice() != b"0" {
        env.book.insert(label.clone(), form.clone());
    }
    if rule.iter().any(|x| *x == label) {
        return Err(logic_error(line, "cyclic deduction".to_string()));
    }
    if rule[0].as_slice() == b"def" {
        Ok(()) // todo: definition(line, book, form, rule[1:], label)
    } else if rule[0].as_slice() == b"axiom" {
        Ok(())
    } else {
        modus_ponens(env, line, form, &rule, hint)
    }
}

fn verify(env: &mut Env, s: &[u8]) -> Result<(), Error> {
    let tokens = scan(&s);
    env.tokens = tokens;
    env.index.set(0);
    parse(env, verify_cb)
}

static RULES: &str = "
hypo. (⊤ ∧ A ⊢ A), axiom.
conj_intro. (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ A ∧ B), axiom.
conj_eliml. (H ⊢ A ∧ B) → (H ⊢ A), axiom.
conj_elimr. (H ⊢ A ∧ B) → (H ⊢ B), axiom.
disj_introl. (H ⊢ A) → (H ⊢ A ∨ B), axiom.
disj_intror. (H ⊢ B) → (H ⊢ A ∨ B), axiom.
disj_elim. (H1 ⊢ A ∨ B) → (H2 ∧ A ⊢ C) → (H3 ∧ B ⊢ C) →
  (H1 ∧ H2 ∧ H3 ⊢ C), axiom.
subj_intro. (H ∧ A ⊢ B) → (H ⊢ A → B), axiom.
subj_elim. (H1 ⊢ A → B) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ B), axiom.
neg_intro. (H ∧ A ⊢ ⊥) → (H ⊢ ¬A), axiom.
neg_elim. (H1 ⊢ ¬A) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ ⊥), axiom.
bij_intro. (H1 ⊢ A → B) → (H2 ⊢ B → A) → (H1 ∧ H2 ⊢ A ↔ B), axiom.
bij_eliml. (H ⊢ A ↔ B) → (H ⊢ A → B), axiom.
bij_elimr. (H ⊢ A ↔ B) → (H ⊢ B → A), axiom.
wk. (H ⊢ B) → (H ∧ A ⊢ B), axiom.
exch. (H ⊢ A) → (H ⊢ A), axiom.
";

fn load_prelude(env: &mut Env) {
    if let Err(_) = verify(env, RULES.as_bytes()) {
        unreachable!();
    }
}

fn main() {
    let argv: Vec<String> = args().collect();
    let mut env = Env::new();
    load_prelude(&mut env);
    for file in &argv[1..] {
        let s = fs::read(file).unwrap();
        if let Err(e) = verify(&mut env, &s) {
            let kind = match e.kind {
                ErrorKind::Syntax => "Syntax",
                ErrorKind::Logic => "Logic"
            };
            println!("{} error in {}, line {}:\n{}",
                kind, file, e.line + 1, e.info);
            break;
        }
    }
}
