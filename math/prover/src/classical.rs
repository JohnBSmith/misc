
use std::collections::{HashSet, HashMap};
use std::fmt::Write;
use std::ops::ControlFlow;
use crate::parser::Prop;
use crate::comb::mappings;

fn variables_rec<'a>(acc: &mut HashSet<&'a str>, t: &'a Prop) {
    match t {
        Prop::Variable(x) => {acc.insert(x);},
        Prop::Not(x) => variables_rec(acc, x),
        Prop::And(t) => {variables_rec(acc, &t.0); variables_rec(acc, &t.1);},
        Prop::Or(t) => {variables_rec(acc, &t.0); variables_rec(acc, &t.1);},
        Prop::Implies(t) => {variables_rec(acc, &t.0); variables_rec(acc, &t.1);},
        Prop::Iff(t) => {variables_rec(acc, &t.0); variables_rec(acc, &t.1);},
        Prop::False => {},
        Prop::True => {}
    }
}

pub fn variables(t: &Prop) -> Vec<&str> {
    let mut acc = HashSet::new();
    variables_rec(&mut acc, t);
    let mut vars: Vec<&str> = acc.into_iter().collect();
    vars.sort();
    vars
}

fn sat(ev: &HashMap<&str, bool>, phi: &Prop) -> bool {
    match phi {
        Prop::Variable(x) => ev[x.as_ref()],
        Prop::False => false,
        Prop::True => true,
        Prop::Not(x) => !sat(ev, x),
        Prop::And(t) => sat(ev, &t.0) && sat(ev, &t.1),
        Prop::Or(t) => sat(ev, &t.0) || sat(ev, &t.1),
        Prop::Implies(t) => !sat(ev, &t.0) || sat(ev, &t.1),
        Prop::Iff(t) => sat(ev, &t.0) == sat(ev, &t.1)
    }
}

pub struct Info {
    pub tautology: bool,
    pub satisfiable: bool
}

pub fn info(phi: &Prop) -> Info {
    let vars = variables(phi);
    let mut info = Info {tautology: true, satisfiable: false};
    mappings(&vars, &[false, true], &mut |_, ev| {
        let y = sat(ev, phi);
        info.tautology &= y;
        info.satisfiable |= y;
        ControlFlow::Continue(())
    });
    info
}

fn line(acc: &mut String, len: usize, c: char) {
    for _ in 0..len {acc.push(c);}
    acc.push('\n');
}

pub fn truth_table(phi: &Prop) -> String {
    let vars = variables(phi);
    let mut acc = String::new();
    let phi_fmt = format!("{}", phi);
    let phi_count = phi_fmt.chars().count();
    let line_len = 2*vars.len() + phi_count + 1;
    let mut lens: Vec<usize> = Vec::new();
    line(&mut acc, line_len, '─');
    for v in &vars {
        let _ = write!(acc, "{} ", v);
        lens.push(v.chars().count());
    }
    let _ = writeln!(acc, " {}", phi_fmt);
    line(&mut acc, line_len, '─');
    mappings(&vars, &[false, true], &mut |t, ev| {
        for (index, x) in t.iter().enumerate() {
            let _ = write!(acc, "{:^1$}", if *x {"1"} else {"0"}, lens[index] + 1);
        }
        let _ = writeln!(acc, " {:^1$}", if sat(ev, phi) {"1"} else {"0"}, phi_count);
        ControlFlow::Continue(())
    });
    line(&mut acc, line_len, '─');
    acc
}

