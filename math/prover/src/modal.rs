
use std::collections::HashSet;
use std::ops::ControlFlow;
use crate::comb::{prod2, power_set, mappings};
use crate::classical::variables_models;
use crate::parser::{Prop, Models};
use crate::intu::{World, Relation, Valuation};
pub use crate::intu::{fmt_worlds, fmt_relation, fmt_valuation};

struct Env<'a> {
    worlds: &'a [World],
    rel: &'a Relation,
    val: Valuation<'a>
}

impl<'a> Env<'a> {
    fn sat(&self, w: World, phi: &Prop) -> bool {
        match phi {
            Prop::Variable(id) => (self.val)(w, id),
            Prop::False => false,
            Prop::True => true,
            Prop::And(t) => self.sat(w, &t.0) && self.sat(w, &t.1),
            Prop::Or(t) => self.sat(w, &t.0) || self.sat(w, &t.1),
            Prop::Implies(t) => !self.sat(w, &t.0) || self.sat(w, &t.1),
            Prop::Not(x) => !self.sat(w, x),
            Prop::Iff(t) => self.sat(w, &t.0) == self.sat(w, &t.1),
            Prop::Nec(x) => self.worlds.iter()
                .filter(|&wp| self.rel.contains(&(w, *wp)))
                .all(|&wp| self.sat(wp, x)),
            Prop::Pos(x) => self.worlds.iter()
                .filter(|&wp| self.rel.contains(&(w, *wp)))
                .any(|&wp| self.sat(wp, x))
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
    let vars = variables_models(models);
    let phi = &models.prop;
    let worlds: Vec<World> = (0..n).map(World).collect();
    power_set(&prod2(&worlds, &worlds), &mut |rel_list| {
        let rel: HashSet<(World, World)> = rel_list.iter().cloned().collect();
        mappings(&prod2(&worlds, &vars), &[false, true], &mut |_, m| {
            let val: Valuation = &|w, v| m[&(w, v)];
            let env = Env {worlds: &worlds, rel: &rel, val};
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
