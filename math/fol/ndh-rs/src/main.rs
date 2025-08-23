
// todo: Definierte Funktion wird auf zu wenige oder viele Argumente angewendet.
// todo: Symboltabelle enthält nur Konstanten. Es wäre zu verhindern,
//   dass bereits definierte Konstanten überschrieben werden.
//   Man beachte auch den Unterschied in der Logik, dass Symbole der
//   Symboltabelle niemals als Muster zur Verfügung stehen. Eigentlich
//   ein gewolltes Verhalten.

use std::{env::args, fs, io::Write};
use std::{rc::Rc, cell::Cell};
use std::collections::HashMap;
use std::process::ExitCode;

mod bstr;
use bstr::Bstr;

mod fmt;

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

fn in_sym3(s: &[u8], i: usize, n: usize) -> Option<Bstr> {
    if i + 2 >= n {return None;}
    match &s[i..i + 3] {
        b"<->" => Some(Bstr::from("↔")),
        _ => None
    }
}

static KEYWORDS: &[(&[u8], &str)] = &[
    (b"Cap", "⋂"),
    (b"Cup", "⋃"),
    (b"and", "∧"),
    (b"cap", "∩"),
    (b"cup", "∪"),
    (b"exists", "∃"),
    (b"false", "⊥"),
    (b"forall", "∀"),
    (b"in", "∈"),
    (b"not", "¬"),
    (b"or", "∨"),
    (b"prod", "∏"),
    (b"sub", "⊆"),
    (b"times", "×"),
    (b"true", "⊤")
];

fn is_utf8_continuation_byte(byte: u8) -> bool {
    (byte & 0b1100_0000) == 0b1000_0000
}

fn decode_utf8_unchecked(s: &[u8]) -> u32 {
    let s0 = s[0];
    if s0 < 0b11100000 {
        // 110xxxxx 10xxxxxx
        (((s0 & 0b11111) as u32) << 6) | ((s[1] & 0b111111) as u32)
    } else {
        // 1110xxxx 10xxxxxx 10xxxxxx
        (((s0 & 0b1111) as u32) << 12)
        | (((s[1] & 0b111111) as u32) << 6)
        |  ((s[2] & 0b111111) as u32)
    }
}

fn mb_is_alpha(s: &[u8]) -> bool {
    let x = decode_utf8_unchecked(s);
    !(x == 172 || x == 215 || (8590..10240).contains(&x))
}

fn unicode_identifier(s: &[u8], mut i: usize, n: usize) -> usize {
    loop {
        if i >= n {return i;}
        if s[i] > 127 {
            let j = i; i += 1;
            while i < n && is_utf8_continuation_byte(s[i]) {i += 1;}
            if !mb_is_alpha(&s[j..i]) {return j;}
        } else if s[i].is_ascii_alphabetic() || s[i].is_ascii_digit() ||
            s[i] == b'_' || s[i] == b'\''
        {
            i += 1;
        } else {return i;}
    }
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
            if i < n && s[i] > 127 {
                i = unicode_identifier(s, i, n);
            }
            let value = match KEYWORDS.binary_search_by_key(&&s[j..i], |t| t.0) {
                Ok(index) => TokenValue::Symbol(Bstr::from(KEYWORDS[index].1)),
                _ => TokenValue::Identifier(Bstr::from(&s[j..i]))
            };
            acc.push(Token {line, value});
        } else if s[i].is_ascii_digit() {
            while i < n && s[i] == b'0' {i += 1;}
            let j = i;
            while i < n && s[i].is_ascii_digit() {
                i += 1;
            }
            let value = TokenValue::Number(if i == j {
                Bstr::from("0")
            } else {
                Bstr::from(&s[j..i])
            });
            acc.push(Token {line, value});
        } else if s[i].is_ascii_whitespace() {
            if s[i] == b'\n' {line += 1;}
            i += 1;
        } else if let Some(x) = in_sym3(s, i, n) {
            let value = TokenValue::Symbol(x);
            acc.push(Token {line, value});
            i += 3;
        } else if let Some(x) = in_sym2(s, i, n) {
            let value = TokenValue::Symbol(x);
            acc.push(Token {line, value});
            i += 2;
        } else if s[i] == b'#' {
            while i < n && s[i] != b'\n' {i += 1;}
        } else if s[i] == b'(' && i + 1 < n && s[i + 1] == b'*' {
            while i < n {
                if s[i] == b'*' && i + 1 < n && s[i + 1] == b')' {
                    i += 2;
                    break;
                }
                if s[i] == b'\n' {line += 1;}
                i += 1;
            }
        } else if s[i] > 127 {
            let j = i; i += 1;
            while i < n && is_utf8_continuation_byte(s[i]) {i += 1;}
            let symbol = &s[j..i];
            let value = if symbol == "∅".as_bytes() {
                TokenValue::Identifier(Bstr::from("empty_set"))
            } else if mb_is_alpha(symbol) {
                i = unicode_identifier(s, i, n);
                TokenValue::Identifier(Bstr::from(&s[j..i]))
            } else {
                TokenValue::Symbol(Bstr::from(symbol))
            };
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
enum Type {None, Some, Prop, Ind, FnSome, Fn(Rc<FnType>)}
use Type::{Prop, Ind};

#[derive(Debug, PartialEq)]
struct FnType {
    argv: Vec<Type>,
    value: Type
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::None => write!(f, "None"),
            Type::Some => write!(f, "Some"),
            Type::Prop => write!(f, "Prop"),
            Type::Ind => write!(f, "Ind"),
            Type::FnSome => write!(f, "FnSome"),
            Type::Fn(t) => {
                if t.argv.len() == 1 {
                    write!(f, "({}", t.argv[0])?;
                } else {
                    for i in 0..t.argv.len() {
                        if i == 0 {
                            write!(f, "({}", t.argv[i])?;
                        } else {
                            write!(f, " × {}", t.argv[i])?;
                        }
                    }
                }
                write!(f, " → {})", t.value)
            }
        }
    }
}

#[derive(Debug)]
struct Substitution {
    term: Term,
    args: Vec<Term>
}

impl Substitution {
    fn call(&self, argv: &[Term]) -> Term {
        substitute_terms(&self.term, &self.args, argv)
    }
}

#[derive(Debug, Clone)]
enum TermValue {
    Var(Bstr),
    Const(Bstr),
    PatVar(Bstr),
    BoundVar(usize),
    App(Rc<[Term]>),
    Forall(Rc<(Term, Term)>),
    Exists(Rc<(Term, Term)>),
    Lambda(Rc<(Term, Term)>),
    Subst(Rc<Substitution>)
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

use TermValue::{
    Var, Const, PatVar, BoundVar, App, Forall, Exists, Lambda, Subst
};

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
    app([constant("conj", prop_prop_prop()), a, b], Prop)
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            if let App(_) = self.value {
                return write!(f, "{:#?}:{}", self.value, self.ty);
            }
        }
        write!(f, "{:?}:{}", self.value, self.ty)
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
            },
            Forall(t) => write!(f, "(forall {} {})", t.0, t.1),
            Exists(t) => write!(f, "(exists {} {})", t.0, t.1),
            Lambda(t) => write!(f, "(lambda {} {})", t.0, t.1),
            Subst(_t) => write!(f, "todo")
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
        let f_ty = fn_type(
            vec![self.args_type.clone(), self.args_type.clone()],
            self.value_type.clone()
        );
        let f = constant(self.ident, f_ty);
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
        ("⋅".as_bytes(), (90, L, infix("mul", Ind, Ind))),
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
        let f_ty = fn_type(vec![self.arg_type.clone()], self.value_type.clone());
        let f = constant(self.ident, f_ty);
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

fn fn_type(argv: Vec<Type>, value: Type) -> Type {
    Type::Fn(Rc::new(FnType {argv, value}))
}

fn prop_prop() -> Type {
    fn_type(vec![Prop], Prop)
}

fn prop_prop_prop() -> Type {
    fn_type(vec![Prop, Prop], Prop)
}

fn ind_ind_prop() -> Type {
    fn_type(vec![Ind, Ind], Prop)
}

fn ind_ind() -> Type {
    fn_type(vec![Ind], Ind)
}

fn ind_ind_ind() -> Type {
    fn_type(vec![Ind, Ind], Ind)
}

fn init_definitions() -> HashMap<Bstr, Type> {
    HashMap::from([
        (Bstr::from("true"), Prop),
        (Bstr::from("false"), Prop),
        (Bstr::from("conj"), prop_prop_prop()),
        (Bstr::from("disj"), prop_prop_prop()),
        (Bstr::from("subj"), prop_prop_prop()),
        (Bstr::from("bijn"), prop_prop_prop()),
        (Bstr::from("neg"), prop_prop()),
        (Bstr::from("nec"), prop_prop()),
        (Bstr::from("pos"), prop_prop()),
        (Bstr::from("seq"), prop_prop_prop()),
        (Bstr::from("nf"), Type::None),
        (Bstr::from("eq"), ind_ind_prop()),
        (Bstr::from("element"), ind_ind_prop()),
        (Bstr::from("comp"), Type::None)
    ])
}

struct Env {
    tokens: Vec<Token>,
    index: Cell<usize>,
    infix_table:  HashMap<&'static [u8], (u32, Assoc, Infix)>,
    prefix_table: HashMap<&'static [u8], (u32, Prefix)>,
    book: HashMap<Bstr, Term>,
    var_counter: Cell<usize>,
    definitions: HashMap<Bstr, Type>,

    #[cfg(debug_assertions)]
    mismatch_trace: std::cell::RefCell<Vec<(Term, Term)>>
}

impl Env {
    fn new() -> Self {
        Self {
            tokens: Vec::new(),
            index: Cell::new(0),
            infix_table: init_infix_table(),
            prefix_table: init_prefix_table(),
            book: HashMap::new(),
            var_counter: Cell::new(0),
            definitions: init_definitions(),

            #[cfg(debug_assertions)]
            mismatch_trace: std::cell::RefCell::new(Vec::new())
        }
    }
    fn lookup(&self) -> &Token {
        &self.tokens[self.index.get()]
    }
    fn advance(&self) {
        self.index.set(self.index.get() + 1);
    }
    fn unique_variable(&self, ty: Type) -> Term {
        self.var_counter.set(self.var_counter.get() + 1);
        term(BoundVar(self.var_counter.get()), ty)
    }

    #[allow(dead_code)]
    fn reset(&mut self) {
        self.book.clear();
        self.definitions = init_definitions();
    }

    #[cfg(debug_assertions)]
    fn set_mismatch(&self, x: Term, y: Term) {
        self.mismatch_trace.borrow_mut().push((x, y));
    }
    #[cfg(debug_assertions)]
    fn print_mismatch(&self) {
        let a = self.mismatch_trace.borrow();
        println!("Traceback:\n");
        for (x, y) in a.iter() {
            println!("     {}\nwith {}\n", x, y);
        }
    }
}

fn substitute_term(t: &Term, x: &Term, u: &Term) -> Term {
    match (&t.value, &x.value) {
        (Var(tv), Var(xv)) if tv == xv => u.clone(),
        (Const(tv), Const(xv)) if tv == xv => u.clone(),
        (BoundVar(tv), BoundVar(xv)) if tv == xv => u.clone(),
        (App(a), _) => term(App(Rc::from(a.iter().map(|s|
            substitute_term(s, x, u)).collect::<Vec<_>>())), t.ty.clone()),
        (Forall(a), _) => term(
            Forall(Rc::new((a.0.clone(), substitute_term(&a.1, x, u)))),
            t.ty.clone()),
        (Exists(a), _) => term(
            Exists(Rc::new((a.0.clone(), substitute_term(&a.1, x, u)))),
            t.ty.clone()),
        (Lambda(a), _) => term(
            Lambda(Rc::new((a.0.clone(), substitute_term(&a.1, x, u)))),
            t.ty.clone()),
        _ => t.clone()
    }
}

fn substitute_terms(t: &Term, x: &[Term], u: &[Term]) -> Term {
    match &t.value {
        Var(tv) => {
            for i in 0..x.len() {
                match &x[i].value {
                    Var(xiv) if tv == xiv => {return u[i].clone();}
                    _ => {}
                }
            }
            t.clone()
        },
        Const(tv) => {
            for i in 0..x.len() {
                match &x[i].value {
                    Const(xiv) if tv == xiv => {return u[i].clone();}
                    _ => {}
                }
            }
            t.clone()
        },
        BoundVar(tv) => {
            for i in 0..x.len() {
                match &x[i].value {
                    BoundVar(xiv) if tv == xiv => {return u[i].clone();}
                    _ => {}
                }
            }
            t.clone()
        },
        App(a) => term(App(Rc::from(a.iter().map(|s|
            substitute_terms(s, x, u)).collect::<Vec<_>>())), t.ty.clone()),
        Forall(a) => term(
            Forall(Rc::new((a.0.clone(), substitute_terms(&a.1, x, u)))),
            t.ty.clone()),
        Exists(a) => term(
            Exists(Rc::new((a.0.clone(), substitute_terms(&a.1, x, u)))),
            t.ty.clone()),
        Lambda(a) => term(
            Lambda(Rc::new((a.0.clone(), substitute_terms(&a.1, x, u)))),
            t.ty.clone()),
        _ => t.clone()
    }
}

fn quantifier(env: &Env, op: fn(Rc<(Term, Term)>) -> TermValue) -> Result<Term, Error> {
    env.advance();
    let token = env.lookup();
    let TokenValue::Identifier(var) = &token.value else {
        return Err(syntax_error(token.line, "expected a variable".to_string()));
    };
    let var = term(Var(var.clone()), Ind);
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") && !token.is_symbol(":") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    let line = token.line;
    let mut x = formula(env, 0)?;
    ensure_type(&mut x, line, &Prop)?;
    let u = env.unique_variable(Ind);
    let x = substitute_term(&x, &var, &u);
    Ok(term(op(Rc::new((u, x))), Prop))
}

fn set_literal(env: &Env, mut x: Term) -> Result<Term, Error> {
    let token = env.lookup();
    ensure_type(&mut x, token.line, &Ind)?;
    x = app([constant("sg", ind_ind()), x], Ind);
    loop {
        let token = env.lookup();
        if !token.is_symbol(",") {break;}
        env.advance();
        let mut y = formula(env, 0)?;
        let token = env.lookup();
        ensure_type(&mut y, token.line, &Ind)?;
        y = app([constant("sg", ind_ind()), y], Ind);
        x = app([constant("union", ind_ind_ind()), x, y], Ind);
    }
    let token = env.lookup();
    if !token.is_symbol("}") {
        return Err(syntax_error(token.line, "expected '}'".to_string()));
    }
    env.advance();
    Ok(x)
}

fn comprehension(env: &Env) -> Result<Term, Error> {
    env.advance();
    let token = env.lookup();
    let line = token.line;
    let mut x = formula(env, 0)?;
    let token = env.lookup();
    if token.is_symbol(",") || token.is_symbol("}") {
        return set_literal(env, x);
    } else if !token.is_symbol("|") {
        return Err(syntax_error(token.line,
            "expected '|'".to_string()));
    }
    let Var(_) = &x.value else {
        return Err(syntax_error(line,
            "expected identifier after '{'".to_string()));
    };
    x.ty = Ind;
    let line = token.line;
    env.advance();
    let mut a = formula(env, 0)?;
    ensure_type(&mut a, line, &Prop)?;
    let token = env.lookup();
    if !token.is_symbol("}") {
        return Err(syntax_error(token.line, "expected '}'".to_string()));
    }
    let u = env.unique_variable(Ind);
    let a = substitute_term(&a, &x, &u);
    let pred = term(Lambda(Rc::new((u, a))), Type::None);
    env.advance();
    Ok(app([constant("comp", Type::None), pred], Ind))
}

fn nud(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    if let TokenValue::Identifier(id) = &token.value {
        env.advance();
        if let Some(ty) = env.definitions.get(id) {
            Ok(term(TermValue::Const(id.clone()), ty.clone()))
        } else {
            Ok(term(TermValue::Var(id.clone()), Type::Some))
        }
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
    } else if token.is_symbol("∀") {
        quantifier(env, Forall)
    } else if token.is_symbol("∃") {
        quantifier(env, Exists)
    } else if token.is_symbol("{") {
        comprehension(env)
    } else {
        if let TokenValue::Symbol(symbol) = &token.value {
            if let Some((bp, op)) = env.prefix_table.get(symbol.as_slice()) {
                env.advance();
                let x = formula(env, *bp)?;
                return op.call(token.line, x);
            }
        } 
        Err(syntax_error(token.line, format!("unimplemented: {:?}", token.value)))
    }
}

fn application(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    let line0 = token.line;
    let x = nud(env)?;
    let mut token = env.lookup();
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
            token = env.lookup();
        }
        if !matches!(&args[0].value, Const(_) | Var(_)) {
            return Err(syntax_error(line0,
                "predicate or function must be an identifier".to_string()));
        }
        args[0].ty = Type::FnSome;
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

fn type_check(line: usize, t: &mut Term, record: &mut HashMap<Bstr, Type>)
-> Result<(), Error>
{
    if let Var(x) = &mut t.value {
        if let Some(ty) = record.get(x) {
            if *ty != t.ty {
                if t.ty == Type::Some {
                    t.ty = ty.clone();
                } else {
                    return Err(logic_error(line, format!(
                        "Type error for {:?}, expected {}, but got {}",
                        t, ty, t.ty)));
                }
            }
        } else if t.ty != Type::Some {
            record.insert(x.clone(), t.ty.clone());
        }
    } else if let App(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        for x in a {
            type_check(line, x, record)?;
        }
        if t.ty == Type::Some {
            t.ty = Ind;
        }
    } else if let Forall(a) | Exists(a) | Lambda(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        type_check(line, &mut a.1, record)?;
    }
    Ok(())
}

// For the remaining variables of Type::Some, set the type to Ind.
fn set_residual_to_ind(t: &mut Term, record: &HashMap<Bstr, Type>) {
    if let Var(x) = &mut t.value {
        if t.ty == Type::Some {
            t.ty = match record.get(x) {
                Some(ty) => ty.clone(),
                None => Ind
            };
        }
    } else if let App(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        for x in a {
            set_residual_to_ind(x, record);
        }
    } else if let Forall(a) | Exists(a) | Lambda(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        set_residual_to_ind(&mut a.1, record);
    }
}

fn type_check_apps(line: usize, t: &mut Term, record: &mut HashMap<Bstr, Type>)
-> Result<(), Error>
{
    if let App(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        if a[0].ty == Type::FnSome {
            let (first, a) = a.split_at_mut(1);
            let f = &mut first[0];
            let fid = match &f.value {
                Const(s) | Var(s) => s,
                _ => panic!()
            };
            f.ty = Type::Fn(Rc::new(FnType {
                argv: a.iter().map(|x| x.ty.clone()).collect(),
                value: t.ty.clone()
            }));
            if let Some(ty) = record.get(fid) {
                if *ty != f.ty {
                    return Err(logic_error(line, format!(
                        "Type error for {:?}: {} != {}", f.value, f.ty, ty)));
                }
            } else {
                record.insert(fid.clone(), f.ty.clone());
            }
        }
        for x in a {
            type_check_apps(line, x, record)?;
        }
    } else if let Forall(a) | Exists(a) | Lambda(a) = &mut t.value {
        let Some(a) = Rc::get_mut(a) else {unreachable!()};
        type_check_apps(line, &mut a.1, record)?;
    }
    Ok(())
}

fn formula_type_checked(env: &Env) -> Result<Term, Error> {
    let token = env.lookup();
    let mut x = formula(env, 0)?;
    ensure_type(&mut x, token.line, &Prop)?;
    let mut record = HashMap::new();
    type_check(token.line, &mut x, &mut record)?;
    set_residual_to_ind(&mut x, &record);
    type_check_apps(token.line, &mut x, &mut HashMap::new())?;
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
        env.advance();
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
    app([constant("seq", prop_prop_prop()), verum(), a], Prop)
}

fn lookup<'a>(book: &'a HashMap<Bstr, Term>, key: &Bstr, line: usize)
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
        Forall(a) => term(
            Forall(Rc::from((a.0.clone(), pattern_from(&a.1)))),
            t.ty.clone()
        ),
        Exists(a) => term(
            Exists(Rc::from((a.0.clone(), pattern_from(&a.1)))),
            t.ty.clone()
        ),
        Lambda(a) => term(
            Lambda(Rc::from((a.0.clone(), pattern_from(&a.1)))),
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
        (Forall(a), Forall(b)) | (Exists(a), Exists(b)) | (Lambda(a), Lambda(b)) => {
            let u = env.unique_variable(Ind);
            let ta = substitute_term(&a.1, &a.0, &u);
            let tb = substitute_term(&b.1, &b.0, &u);
            term_eq(env, &ta, &tb)
        },
        _ => false
    }
}

mod substi {
    use crate::{Term, Bstr};
    #[derive(Clone, Debug)]
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

fn side_condition<'a>(c: &'a Term, conds: &mut Vec<(Term, Term)>) -> &'a Term {
    if c.is_connective("subj") && c.arg(1).is_connective("nf") {
        let x = c.arg(1).arg(1);
        let a = c.arg(1).arg(2);
        conds.push((x.clone(), a.clone()));
        side_condition(c.arg(2), conds)
    } else {c}
}

fn free_in(env: &Env, x: &Term, t: &Term, subs: &Subs) -> bool {
    match &t.value {
        PatVar(id) => {
            if let Some(t_subs) = subs.get(id) {
                if !term_eq(env, t, t_subs) {
                    return free_in(env, x, t_subs, subs);
                }
            }
            t.ty == Ind && term_eq(env, x, t)
        },
        Var(_) | Const(_) => {
            t.ty == Ind && term_eq(env, x, t)
        },
        App(a) => {
            for s in a.iter() {
                if free_in(env, x, s, subs) {return true;}
            }
            false
        },
        Forall(a) | Exists(a) | Lambda(a) => free_in(env, x, &a.1, subs),
        _ => false
    }
}

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

#[cfg(debug_assertions)]
macro_rules! trace {
    ($env:expr, $x:expr, $y:expr) => {$env.set_mismatch($x.clone(), $y.clone())}
}

#[cfg(not(debug_assertions))]
macro_rules! trace {
    ($env:expr, $x:expr, $y:expr) => {}
}

fn unify_seq(env: &Env, line: usize, a: &[Term], pattern: &[Term], subs: &mut Subs)
-> bool
{
    let result = unify(env, line, &a[2], &pattern[2], subs);
    if !result {trace!(env, a[2], pattern[2]); return false;}
    let mut l1 = Vec::new();
    let mut l2 = Vec::new();
    conj_list(&pattern[1], Some(subs), &mut l2);
    conj_list(&a[1], None, &mut l1);
    set_eq(env, &l1, &l2)
}

fn unify_args(env: &Env, line: usize, a: &[Term], b: &[Term], subs: &mut Subs)
-> bool
{
    if a.len() != b.len() {
        trace!(env,
            term(App(Rc::from(a)), Type::None),
            term(App(Rc::from(b)), Type::None));
        return false;
    }
    let mut subs_copy = subs.clone();
    for (x, pat) in a.as_ref().iter().zip(b.as_ref()) {
        let result = unify(env, line, x, pat, subs);
        if !result {
            if a[0].is_const("seq") && b[0].is_const("seq") {
                let result = unify_seq(env, line, a, b, &mut subs_copy);
                if result {
                    subs.set_to(subs_copy);
                }
                return result;
            }
            trace!(env,
                term(App(Rc::from(a)), Type::None),
                term(App(Rc::from(b)), Type::None));
            return false;
        }
    }
    true
}

fn unify_pred(env: &Env, line: usize, t: &Term, pattern: &[Term], subs: &mut Subs)
-> bool
{
    let PatVar(f) = &pattern[0].value else {unreachable!()};
    let args = &pattern[1..];
    if let Some(f) = subs.get(f) {
        let Subst(f) = &f.value else {
            trace!(env, t, term(App(Rc::from(pattern)), t.ty.clone()));
            return false
        };
        let b = f.call(args);
        unify(env, line, t, &b, subs)
    } else {
        let mut acc = Vec::with_capacity(args.len());
        for x in args {
            if let PatVar(id) = &x.value {
                if let Some(x) = subs.get(id) {
                    acc.push(x.clone());
                } else {
                    acc.push(x.clone());
                }
            } else {
                acc.push(x.clone());
            }
        }
        subs.set(f.clone(), term(Subst(Rc::new(Substitution {term: t.clone(), args: acc})), Type::None));
        true
    }
}

fn unify_quant(env: &Env, line: usize, t: &(Term, Term), pattern: &(Term, Term), subs: &mut Subs)
-> bool
{
    let u = env.unique_variable(Ind);
    let ta = substitute_term(&t.1, &t.0, &u);
    let tb = substitute_term(&pattern.1, &pattern.0, &u);
    unify(env, line, &ta, &tb, subs)
}

fn unify(env: &Env, line: usize, t: &Term, pattern: &Term, subs: &mut Subs)
-> bool
{
    // println!("    {}\nmit {}\n", t, pattern);
    if pattern.ty != t.ty {
        trace!(env, t, pattern);
        return false;
        // return Err(logic_error(line, format!("type error {pattern:?}, {t:?}")));
    }
    match &pattern.value {
        PatVar(id) => {
            if let Some(b) = subs.get(id) {
                term_eq(env, t, b)
            } else {
                subs.set(id.clone(), t.clone());
                true
            }
        },
        App(b) => {
            if let PatVar(_) = &b[0].value {
                return unify_pred(env, line, t, b, subs);
            }
            match &t.value {
                App(a) => unify_args(env, line, a, b, subs),
                _ => {trace!(env, t, pattern); false}
            }
        },
        Forall(b) => match &t.value {
            Forall(a) => unify_quant(env, line, a, b, subs),
            _ => {trace!(env, t, pattern); false}
        },
        Exists(b) => match &t.value {
            Exists(a) => unify_quant(env, line, a, b, subs),
            _ => {trace!(env, t, pattern); false}
        },
        Lambda(b) => match &t.value {
            Lambda(a) => unify_quant(env, line, a, b, subs),
            _ => {trace!(env, t, pattern); false}
        },
        _ => term_eq(env, pattern, t)
    }
}

fn unification_hint(line: usize, hint: &Term, subs: &mut Subs)
-> Result<(), Error>
{
    if hint.is_connective("bijn") || hint.is_connective("eq") {
        let lhs = hint.arg(1); let rhs = hint.arg(2);
        if let App(a) = &lhs.value {
            let f = &a[0]; let args = &a[1..];
            if let Var(id) = &f.value {
                let subst = Rc::new(Substitution {term: rhs.clone(), args: args.to_vec()});
                subs.set(id.clone(), term(Subst(subst), Type::None));
            }
            return Ok(());
        }
    }
    Err(logic_error(line, format!("invalid unification hint: {}", hint)))
}

fn is_quantifier_rule(c: &Term) -> bool {
    if c.is_connective("subj") && c.arg(2).is_connective("seq") {
        let a = c.arg(2).arg(2);
        matches!(&a.value, Forall(_) | Exists(_))
    } else {false}
}

fn gen_schema_variable(i: usize) -> Term {
    term(Var(Bstr::from(format!("H{}*", i).as_str())), Prop)
}

fn nested_conj(i: usize, n: usize) -> Term {
    let head = gen_schema_variable(i);
    if i == n {
        head
    } else {
        app([constant("conj", prop_prop_prop()), head, nested_conj(i + 1, n)], Prop)
    }
}

fn auto_rule(line: usize, a: &Term, i: usize, n: usize) -> Result<Term, Error> {
    if i == n + 1 {
        Ok(app([constant("seq", prop_prop_prop()), nested_conj(1, n), a.clone()], Prop))
    } else if a.is_connective("subj") {
        let head = app([constant("seq", prop_prop_prop()), gen_schema_variable(i), a.arg(1).clone()], Prop);
        let tail = auto_rule(line, a.arg(2), i + 1, n)?;
        Ok(app([constant("subj", prop_prop_prop()), head, tail], Prop))
    } else {
        Err(logic_error(line, format!(
            "expected a subjunction for premise {}", i)))
    }
}

fn conclusion(env: &Env, line: usize, b: &Term, c: &Term, subs: &mut Subs, args: &[Bstr])
-> Result<(), Error>
{
    #[cfg(debug_assertions)]
    env.mismatch_trace.borrow_mut().clear();

    let result = unify(env, line, b, c, subs);
    if !result {
        #[cfg(debug_assertions)] {
            env.print_mismatch();
        }
        return Err(logic_error(line,
            format!("unification failed for {}, in conclusion", args[0])));
    }
    Ok(())
}

fn modus_ponens(env: &Env, line: usize, b: &Term, args: &[Bstr], hint: Option<Term>)
-> Result<(), Error>
{
    let c = lookup(&env.book, &args[0], line)?;
    let c0 = if args.len() > 1 && c.is_connective("seq") {
        if !c.arg(1).is_const("true") {
            return Err(logic_error(line,
                format!("'{}' does not correspond to a rule", args[0])));
        }
        pattern_from(&auto_rule(line, c.arg(2), 1, args.len() - 1)?)
    } else {
        pattern_from(c)
    };
    let mut conds: Vec<(Term, Term)> = Vec::new();
    let mut c = side_condition(&c0, &mut conds);
    // println!("{c:#?}");

    let mut subs = Subs::new();
    let mut reverse = false;
    if let Some(hint) = hint {
        unification_hint(line, &hint, &mut subs)?;
    }
    if is_quantifier_rule(c) {
        conclusion(env, line, b, c.arg(2), &mut subs, args)?;
        reverse = true;
    }
    for i in 1..args.len() {
        let a = lookup(&env.book, &args[i], line)?;
        if !c.is_connective("subj") {
            return Err(logic_error(line, "expected a rule/subjunction".to_string()));
        }

        #[cfg(debug_assertions)]
        env.mismatch_trace.borrow_mut().clear();

        let result = unify(env, line, a, c.arg(1), &mut subs);
        if !result {
            #[cfg(debug_assertions)] {
                env.print_mismatch();
            }
            return Err(logic_error(line,
                format!("unification failed for {}, argument {}", args[0], i)));
        }
        c = c.arg(2);
    }
    if !reverse {
        conclusion(env, line, b, c, &mut subs, args)?;
    }
    for (x, a) in &conds {
        let mut x = x;
        if let PatVar(id) = &x.value {
            if let Some(x_subs) = subs.get(id) {
                x = x_subs;
            }
        }
        // println!("COND: {} in {:?}", x, a);
        // println!("SUBS: {:#?}", subs);
        if free_in(env, x, a, &subs) {
            return Err(logic_error(line, format!(
                "in {}: {} occurs free in {}", args[0], x, a)));
        }
    }
    Ok(())
}

fn expect_len(line: usize, args: &[Bstr], n: usize, rule_name: &str)
-> Result<(), Error>
{
    let s = if n == 1 {""} else {"s"};
    Err(logic_error(line, format!(
        "rule {} expects {} argument{}, but got {}",
        rule_name, n, s, args.len())))
}

fn free_vars(env: &Env, a: &Term, s: &mut HashMap<Bstr, ()>) {
    match &a.value {
        Var(id) | Const(id) => {
            if !env.definitions.contains_key(id) {
                s.insert(id.clone(), ());
            }
        },
        App(a) => {
            for b in a.iter() {
                free_vars(env, b, s);
            }
        },
        Forall(a) | Exists(a) | Lambda(a) => {
            free_vars(env, &a.1, s);
        },
        _ => {}
    }
}

fn free_vars_check(env: &Env, line: usize, a: &Term, argv: &[Term], label: &Bstr) -> Result<(), Error> {
    let mut s = HashMap::new();
    free_vars(env, a, &mut s);
    for x in s.keys() {
        if label.as_slice() != "0".as_bytes() &&
            !argv.iter().any(|arg|
                matches!(&arg.value, Const(id) | Var(id) if id == x))
        {
            println!("{:?}", a);
            return Err(logic_error(line, format!(
                "{} is free in right hand side of definition", x)));
        }
    }
    Ok(())
}

fn theorem_sequent(t: Term) -> Term {
    app([constant("seq", prop_prop_prop()), verum(), t], Prop)
}

fn definition(env: &mut Env, line: usize, seq: &mut Term, args: &[Bstr], label: &Bstr)
-> Result<(), Error>
{
    if args.len() != 1 {
        return expect_len(line, args, 0, "def");
    }
    if !seq.is_connective("seq") {
        return Err(logic_error(line, "definition expects a sequent".to_string()));
    }
    if !seq.arg(1).is_const("true") {
        return Err(logic_error(line, "definition expects empty context".to_string()));
    }
    let c = seq.arg(2);
    if c.is_connective("bijn") || c.is_connective("eq") {
        let con = c.arg(0); let a = c.arg(1); let b = c.arg(2);
        match &a.value {
            Var(id) | Const(id) =>  {
                if env.definitions.contains_key(id) {
                    return Err(logic_error(line, "already defined".to_string()));
                }
                free_vars_check(env, line, b, &[], label)?;
                env.definitions.insert(id.clone(), a.ty.clone());
                *seq = theorem_sequent(app([
                    con.clone(),
                    term(Const(id.clone()), a.ty.clone()),
                    b.clone()
                ], c.ty.clone()));
            },
            App(args) => {
                let (Var(id) | Const(id)) = &args[0].value else {
                    return Err(logic_error(line, "expected identifier".to_string()));
                };
                if env.definitions.contains_key(id) {
                    return Err(logic_error(line, "already defined".to_string()));
                }
                free_vars_check(env, line, b, &args[1..], label)?;
                env.definitions.insert(id.clone(), args[0].ty.clone());
                let mut args = args.to_vec();
                args[0] = term(Const(id.clone()), args[0].ty.clone());
                *seq = theorem_sequent(app([
                    con.clone(),
                    term(App(Rc::from(args)), a.ty.clone()),
                    b.clone()
                ], c.ty.clone()));
            },
            _ => {
                return Err(logic_error(line, "malformed definition".to_string()));
            }
        }
    } else {
        return Err(logic_error(line, "malformed definition".to_string()));
    }
    Ok(())
}

fn verify_cb(env: &mut Env, stmt: Statement) -> Result<(), Error> {
    let Statement {line, label, term, rule, hint} = stmt;
    // println!("{:#?}", term);
    let mut form = match term {
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
            app([constant("seq", prop_prop_prop()), h, a], Prop)
        },
        Sum::Left(form) => form
    };
    if rule.iter().any(|x| *x == label) {
        return Err(logic_error(line, "cyclic deduction".to_string()));
    }
    if rule[0].as_slice() == b"def" {
        definition(env, line, &mut form, &rule, &label)?;
    } else if rule[0].as_slice() == b"axiom" {
    } else {
        modus_ponens(env, line, &form, &rule, hint)?;
    }
    if label.as_slice() != b"0" {
        env.book.insert(label.clone(), form);
    }
    Ok(())
}

fn verify(env: &mut Env, s: &[u8]) -> Result<(), Error> {
    let tokens = scan(s);
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
uq_intro. (nf u (H ∧ ∀x. A x)) → (H ⊢ A u) → (H ⊢ ∀x. A x), axiom.
uq_elim. (H ⊢ ∀x. A x) → (H ⊢ A t), axiom.
ex_intro. (H ⊢ A t) → (H ⊢ ∃x. A x), axiom.
ex_elim. (nf u (H1 ∧ H2 ∧ B ∧ ∃x. A x)) →
  (H1 ⊢ ∃x. A x) → (H2 ∧ A u ⊢ B) → (H1 ∧ H2 ⊢ B), axiom.
lift_impl. (⊢ A → B) → (H ⊢ A) → (H ⊢ B), axiom.
lift_impl_ii. (⊢ A → B → C) → (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ C), axiom.
";

#[allow(dead_code)]
fn load_prelude(env: &mut Env) {
    if verify(env, RULES.as_bytes()).is_err() {
        unreachable!();
    }
}

fn main() -> ExitCode {
    let argv: Vec<String> = args().collect();
    if argv.len() >= 3 && argv[1] == "-f" {
        let s = fs::read(&argv[2]).unwrap();
        let fs = fmt::format_source_code(&s);
        let opath = &argv[if argv.len() == 4 {3} else {2}];
        let mut fout = fs::File::create(opath).unwrap();
        fout.write_all(&fs).unwrap();
        if opath == "/dev/stdout" {
            fout.write_all(b"\n").unwrap();
        }
    } else {
        let mut env = Env::new();
        load_prelude(&mut env);
        for file in &argv[1..] {
            let s = match fs::read(file) {
                Ok(value) => value,
                Err(e) => {
                    println!("Could not read file {}, error kind: {}.",
                        file, e.kind());
                    return ExitCode::FAILURE;
                }
            };
            if let Err(e) = verify(&mut env, &s) {
                let kind = match e.kind {
                    ErrorKind::Syntax => "Syntax",
                    ErrorKind::Logic => "Logic"
                };
                println!("{} error in {}, line {}:\n{}",
                    kind, file, e.line + 1, e.info);
                return ExitCode::FAILURE;
            }
        }
    }
    ExitCode::SUCCESS
}
