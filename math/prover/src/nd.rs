
use std::fmt::Write;
use std::rc::Rc;
use std::collections::HashSet;
use crate::parser::Prop;

#[derive(Debug, Clone)]
struct Sequent {
    env: Vec<Prop>,
    prop: Box<Prop>
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Proof {
    from: Vec<Proof>,
    seq: Box<Sequent>
}

impl Sequent {
    fn new(env: &[Prop], prop: &Prop) -> Self {
        Self {env: Vec::from(env), prop: Box::new(prop.clone())}
    }
}

impl Proof {
    fn new(from: Vec<Proof>, seq: Sequent) -> Self {
        Self {from, seq: Box::new(seq)}
    }
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut comma = "";
        for phi in &self.env {
            write!(f, "{}{}", comma, phi)?;
            comma = ", ";
        }
        write!(f, " ⊢ {}", self.prop)
    }
}

fn fmt_proof_rec(buf: &mut String, p: &Proof, indent: usize) {
    let _ = write!(buf, "{:<1$}", "", indent);
    let _ = writeln!(buf, "{}", p.seq);
    for pi in &p.from {
        fmt_proof_rec(buf, pi, indent + 4);
    }
} 

impl std::fmt::Display for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut acc =  String::new();
        fmt_proof_rec(&mut acc, self, 0);
        write!(f, "{}", acc)
    }
}

fn conj(a: &Prop, b: &Prop) -> Prop {
    Prop::And(Rc::new((a.clone(), b.clone())))
}

fn cond(a: &Prop, b: &Prop) -> Prop {
    Prop::Implies(Rc::new((a.clone(), b.clone())))
}

fn add_env_prop(env: &[Prop], phi: &Prop) -> Vec<Prop> {
    let mut acc = Vec::with_capacity(env.len() + 1);
    for x in env {
        acc.push(x.clone());
    }
    acc.push(phi.clone());
    acc
}

fn env_contains(env: &[Prop], phi: &Prop) -> Option<usize> {
    for (index, x) in env.iter().enumerate() {
        if x == phi {return Some(index);}
    }
    None
}

fn find_destruct(env: &[Prop], prop: &Prop, max_depth: u32) -> Option<Proof> {
    match prop {
        Prop::Implies(t) => {
            let pi = find_rec(&add_env_prop(env, &t.0), &t.1, max_depth)?;
            Some(Proof::new(vec![pi], Sequent::new(env, prop)))
        },
        Prop::Not(x) => {
            let pi = find_rec(&add_env_prop(env, x), &Prop::False, max_depth)?;
            Some(Proof::new(vec![pi], Sequent::new(env, prop)))
        },
        Prop::And(t) => {
            let pi0 = find_rec(env, &t.0, max_depth)?;
            let pi1 = find_rec(env, &t.1, max_depth)?;
            Some(Proof::new(vec![pi0, pi1], Sequent::new(env, prop)))
        },
        Prop::Or(t) => {
            if let Some(pi) = find_rec(env, &t.0, max_depth) {
                return Some(Proof::new(vec![pi], Sequent::new(env, prop)))
            }
            if let Some(pi) = find_rec(env, &t.1, max_depth) {
                return Some(Proof::new(vec![pi], Sequent::new(env, prop)))
            }
            None
        },
        Prop::Iff(t) => {
            let pi0 = find_rec(env, &cond(&t.0, &t.1), max_depth)?;
            let pi1 = find_rec(env, &cond(&t.1, &t.0), max_depth)?;
            Some(Proof::new(vec![pi0, pi1], Sequent::new(env, prop)))
        },
        _ => None
    }
}

fn complexity(pi: &Proof) -> u32 {
    if let Some(value) = pi.from.iter().map(complexity).max() {
        return 1 + value;
    } else {
        return 0;
    }
}

fn parts_rec(acc: &mut HashSet<Prop>, phi: &Prop) {
    acc.insert(phi.clone());
    match phi {
        Prop::And(t) => {parts_rec(acc, &t.0); parts_rec(acc, &t.1);}
        _ => {}
    }
}

fn parts(env: &[Prop]) -> HashSet<Prop> {
    let mut acc = HashSet::new();
    for phi in env {
        parts_rec(&mut acc, phi);
    }
    acc
}

fn find_rec(env: &[Prop], prop: &Prop, max_depth: u32) -> Option<Proof> {
    if let Some(_) = env_contains(env, &prop) {
        return Some(Proof::new(vec![], Sequent::new(env, prop)));
    }
    let result = find_destruct(env, prop, max_depth);
    if result.is_some() {return result;}
    if max_depth != 0 {
        let mut proofs: Vec<Proof> = Vec::new();
        let s = parts(env);
        for phi in &s {
            if let Some(pi) = find_rec(env, &conj(phi, prop), max_depth - 1) {
                proofs.push(Proof::new(vec![pi], Sequent::new(env, prop)));
            }
            if let Some(pi) = find_rec(env, &conj(prop, phi), max_depth - 1) {
                proofs.push(Proof::new(vec![pi], Sequent::new(env, prop)));
            }
            if let Prop::Implies(t) = phi {
                if &t.1 == prop {
                    if let Some(pi0) = find_rec(env, phi, max_depth - 1) {
                        if let Some(pi1) = find_rec(env, &t.0, max_depth - 1) {
                            proofs.push(Proof::new(vec![pi0, pi1], Sequent::new(env, prop)));
                        }
                    }
                }
            }
        }
        if let Some(pi) = proofs.iter().min_by_key(|&x| complexity(x)) {
            return Some(pi.clone());
        }
    }
    None
}

pub fn find_proof(phi: &Prop) -> Option<Proof> {
    find_rec(&[], phi, 2)
}

