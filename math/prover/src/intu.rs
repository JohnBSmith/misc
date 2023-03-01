
use std::collections::HashSet;
use std::hash::Hash;
use std::fmt::Write;
use std::ops::ControlFlow;
use crate::comb::{prod2, power_set, mappings};
use crate::classical::variables_models;
use crate::parser::{Prop, Models};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct World(pub u32);
pub type Relation = HashSet<(World, World)>;
pub type Valuation<'a> = &'a dyn Fn(World, &str) -> bool;

impl std::fmt::Display for World {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "w{}", self.0)
    }
}

pub fn fmt_worlds(worlds: &[World]) -> String {
    let mut acc: String = String::from("{");
    let mut first = true;
    for &w in worlds {
        if first {first = false;} else {acc.push_str(", ");}
        let _ = write!(acc, "{}", w);
    }
    acc.push('}');
    acc
}

pub fn fmt_relation(rel: &[(World, World)]) -> String {
    let mut acc: String = String::from("{");
    let mut first = true;
    for (x, y) in rel {
        if first {first = false;} else {acc.push_str(", ");}
        let _ = write!(acc, "({}, {})", x, y);
    }
    acc.push('}');
    acc
}

pub fn fmt_valuation(worlds: &[World], vars: &[&str], val: Valuation) -> String {
    let mut acc: String = String::from("{\n    ");
    let mut first_line = true;
    let mut count = 0;
    let n = vars.len()*worlds.len();
    for v in vars {
        if first_line {first_line = false} else {acc.push_str("\n    ");}
        for &w in worlds {
            let _ = write!(acc, "({}, {}): {}", w, v, if val(w, v) {"1"} else {"0"});
            count += 1;
            if count != n {acc.push_str(", ");}
        }
    }
    acc.push_str("\n}");
    acc
}

fn is_reflexive(worlds: &[World], rel: &Relation) -> bool {
    worlds.iter().all(|&x| rel.contains(&(x, x)))
}

fn is_transitive(worlds: &[World], rel: &Relation) -> bool {
    for &x in worlds {
        for &y in worlds {
            for &z in worlds {
                let cond =  !(rel.contains(&(x, y)) && rel.contains(&(y, z)))
                    || rel.contains(&(x, z));
                if !cond {return false;}
            }
        }
    }
    true        
}

fn is_preorder(worlds: &[World], rel: &Relation) -> bool {
    is_reflexive(worlds, rel) && is_transitive(worlds, rel)
}

fn preorders(worlds: &[World],
    cb: &mut dyn FnMut(&[(World, World)], &HashSet<(World, World)>) -> ControlFlow<()>
) -> ControlFlow<()>
{
    power_set(&prod2(worlds, worlds), &mut |s| {
        let rel: HashSet<(World, World)> = s.iter().cloned().collect();
        if is_preorder(worlds, &rel) {
            cb(s, &rel)?;
        }
        ControlFlow::Continue(())
    })
}

fn is_monotonic(
    val: Valuation,
    vars: &[&str],
    worlds: &[World],
    rel: &Relation
) -> bool
{
    for v in vars {
        for &w in worlds {
            for &wp in worlds {
                if rel.contains(&(w, wp)) && !(!val(w, v) || val(wp, v)) {
                    return false;
                }
            }
        }
    }
    true
}

fn monotonic_mappings(vars: &[&str], worlds: &[World],
    rel: &Relation, cb: &mut dyn FnMut(Valuation) -> ControlFlow<()>
) -> ControlFlow<()>
{
    mappings(&prod2(worlds, vars), &[false, true], &mut |_, m| {
        let val: Valuation = &|w, v| m[&(w, v)];
        if is_monotonic(val, vars, worlds, rel) {
            cb(val)?;
        }
        ControlFlow::Continue(())
    })
}

struct Env<'a> {
    worlds: &'a [World],
    rel: &'a Relation,
    val: Valuation<'a>
}

impl<'a> Env<'a> {
    fn sat_implies(&self, w: World, a: &Prop, b: &Prop) -> bool {
        self.worlds.iter().filter(|&wp| self.rel.contains(&(w, *wp))).all(|&wp|
            !self.sat(wp, a) || self.sat(wp, b))
    }
    fn sat(&self, w: World, phi: &Prop) -> bool {
        match phi {
            Prop::Variable(id) => (self.val)(w, id),
            Prop::False => false,
            Prop::True => true,
            Prop::And(t) => self.sat(w, &t.0) && self.sat(w, &t.1),
            Prop::Or(t) => self.sat(w, &t.0) || self.sat(w, &t.1),
            Prop::Implies(t) => self.sat_implies(w, &t.0, &t.1),
            Prop::Not(x) =>
                self.worlds.iter().filter(|&wp| self.rel.contains(&(w, *wp))).all(|&wp|
                    !self.sat(wp, x)),
            Prop::Iff(t) => self.sat_implies(w, &t.0, &t.1)
                         && self.sat_implies(w, &t.1, &t.0),
            Prop::Nec(_) => unimplemented!(),
            Prop::Pos(_) => unimplemented!()
        }
    }
    fn sat_env(&self, w: World, env: &[Prop]) -> bool {
        env.iter().all(|phi| self.sat(w, phi))
    }
}

fn try_find_countermodel_at(models: &Models, n: u32,
    cb: &mut dyn FnMut(&[World], World, &[(World, World)], Valuation, &[&str])
) -> ControlFlow<()>
{
    let phi = &models.prop;
    let vars = variables_models(models);
    let worlds: Vec<World> = (0..n).map(World).collect();
    preorders(&worlds, &mut |rel_list, rel| {
        monotonic_mappings(vars.as_ref(), &worlds, rel, &mut |val| {
            let env = Env {worlds: &worlds, rel, val};
            for &w in &worlds {
                if env.sat_env(w, &models.env) && !env.sat(w, phi) {
                    cb(&worlds, w, rel_list, val, &vars);
                    return ControlFlow::Break(());
                }
            }
            ControlFlow::Continue(())
        })
    })
}

pub fn try_find_countermodel(models: &Models,
    cb: &mut dyn FnMut(&[World], World, &[(World, World)], Valuation, &[&str])
) {
    for n in 0..4 {
        if try_find_countermodel_at(models, n, cb).is_break() {return;}
    }
}
