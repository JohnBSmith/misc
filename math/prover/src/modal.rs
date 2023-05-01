
use std::collections::HashSet;
use std::ops::ControlFlow;
use crate::comb::{prod2, power_set, mappings};
use crate::classical::variables_models;
use crate::parser::{Prop, Models};
use crate::intu::{World, Relation, Valuation};
use crate::LogicalSystem;
pub use crate::intu::{fmt_worlds, fmt_relation, fmt_valuation,
    is_reflexive, is_transitive};

fn is_symmetric(worlds: &[World], rel: &Relation) -> bool {
    for &x in worlds {
        for &y in worlds {
            if rel.contains(&(x, y)) && !rel.contains(&(y, x)) {
                return false;
            }
        }
    }
    true
}

fn is_euclidean(worlds: &[World], rel: &Relation) -> bool {
    for &x in worlds {
        for &y in worlds {
            for &z in worlds {
                let cond = !(rel.contains(&(x, y)) && rel.contains(&(x, z)))
                    || rel.contains(&(y, z));
                if !cond {
                    return false;
                }
            }
        }
    }
    true
}

fn is_serial(worlds: &[World], rel: &Relation) -> bool {
    for &x in worlds {
        if !worlds.iter().any(|&y| rel.contains(&(x, y))) {
            return false;
        }
    }
    true
}

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

fn relations(worlds: &[World], system: LogicalSystem,
    cb: &mut dyn FnMut(&[(World, World)], &Relation) -> ControlFlow<()>
) -> ControlFlow<()>
{
    match system {
        LogicalSystem::K => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                cb(rel_as_list, &rel)
            })
        },
        LogicalSystem::T => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                if is_reflexive(worlds, &rel) {
                    cb(rel_as_list, &rel)?;
                }
                ControlFlow::Continue(())
            })
        },
        LogicalSystem::S4 => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                if is_reflexive(worlds, &rel) && is_transitive(worlds, &rel) {
                    cb(rel_as_list, &rel)?;
                }
                ControlFlow::Continue(())
            })
        },
        LogicalSystem::S5 => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                if is_reflexive(worlds, &rel) && is_euclidean(worlds, &rel) {
                    cb(rel_as_list, &rel)?;
                }
                ControlFlow::Continue(())
            })
        },
        LogicalSystem::B => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                if is_reflexive(worlds, &rel) && is_symmetric(worlds, &rel) {
                    cb(rel_as_list, &rel)?;
                }
                ControlFlow::Continue(())
            })
        },
        LogicalSystem::D => {
            power_set(&prod2(worlds, worlds), &mut |rel_as_list| {
                let rel: HashSet<(World, World)> = rel_as_list.iter().cloned().collect();
                if is_serial(worlds, &rel) {
                    cb(rel_as_list, &rel)?;
                }
                ControlFlow::Continue(())
            })
        },
        _ => unreachable!()
    }
}

fn try_find_countermodel_at(models: &Models, n: u32, system: LogicalSystem,
    cb: &mut dyn FnMut(&[World], World, &[(World, World)], Valuation, &[&str])
) -> ControlFlow<()>
{
    let vars = variables_models(models);
    let phi = &models.prop;
    let worlds: Vec<World> = (0..n).map(World).collect();
    relations(&worlds, system, &mut |rel_as_list, rel| {
        mappings(&prod2(&worlds, &vars), &[false, true], &mut |_, m| {
            let val: Valuation = &|w, v| m[&(w, v)];
            let env = Env {worlds: &worlds, rel, val};
            for &w in &worlds {
                if env.sat_env(w, &models.env) && !env.sat(w, phi) {
                    cb(&worlds, w, rel_as_list, val, &vars);
                    return ControlFlow::Break(());
                }
            }
            ControlFlow::Continue(())
        })
    })
}

pub fn try_find_countermodel(models: &Models, system: LogicalSystem, worlds_max: u32,
    cb: &mut dyn FnMut(&[World], World, &[(World, World)], Valuation, &[&str])
) {
    for n in 0..worlds_max+1 {
        if try_find_countermodel_at(models, n, system, cb).is_break() {return;}
    }
}
