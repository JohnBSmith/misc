
mod parser;
pub mod comb;
mod nd;

mod classical;
mod intu;
mod modal;

#[cfg(test)]
mod test;

use parser::{parse, AST, Models};
use classical::truth_table;

fn input(prompt: &str) -> String {
    use std::{io, io::Write};
    let mut buffer = String::new();
    print!("{}", prompt);
    io::stdout().flush().unwrap();
    io::stdin().read_line(&mut buffer).unwrap();
    if buffer.ends_with('\n') {
        buffer.pop();
        if buffer.ends_with('\r') {buffer.pop();}
    }
    buffer
}

#[derive(Clone, Copy)]
pub enum LogicalSystem {None, K, T, S4, S5, B, D}
impl std::fmt::Display for LogicalSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", match self {
            Self::K => "K",
            Self::T => "T",
            Self::S4 => "S4",
            Self::S5 => "S5",
            Self::B => "B",
            Self::D => "D",
            Self::None => "none"
        })
    }
}

pub struct Config {
    system: LogicalSystem,
    worlds_max: u32
}

impl Config {
    fn from_args() -> Result<Self, String> {
        const WORLDS_MAX_DEFAULT: u32 = 3;
        let mut config = Self {
            system: LogicalSystem::None,
            worlds_max: WORLDS_MAX_DEFAULT
        };
        for arg in std::env::args().skip(1) {
            if let Ok(n) = arg.parse::<u32>() {
                config.worlds_max = n;
            } else {
                let system = match arg.as_ref() {
                    "K" => LogicalSystem::K,
                    "T" => LogicalSystem::T,
                    "S4" => LogicalSystem::S4,
                    "S5" => LogicalSystem::S5,
                    "B" => LogicalSystem::B,
                    "D" => LogicalSystem::D,
                    s => return Err(s.to_string())
                };
                config.system = system;
            }
        }
        Ok(config)
    }
}

fn standard_analysis_model_rel(models: &Models, worlds_max: u32) {
    println!("Presented statement:\n  {}\n", models);
    intu::try_find_countermodel(models, worlds_max, &mut |worlds, w, rel, val, vars| {
        println!("COUNTERMODEL (Kripke semantics)");
        println!("Worlds: {};", intu::fmt_worlds(worlds));
        println!("Relation: {};", intu::fmt_relation(rel));
        println!("Valuation: {};", intu::fmt_valuation(worlds, vars, val));
        println!("{} does not satisfy the formula.", w);
    });
}

fn standard_analysis(s: &str, worlds_max: u32) {
    match parse(s.as_bytes()) {
        Ok(phi) => {
            let AST::Prop(phi) = phi else {
                if let AST::Models(models) = phi {
                    standard_analysis_model_rel(&models, worlds_max);
                }
                return;
            };
            println!("Presented formula:\n  {}\n", phi);
            let info = classical::info(&phi);
            println!("It is{} a tautology.",
                if info.tautology {""} else {" not"});
            if !info.tautology {
                println!("It is{} satisfiable.",
                    if info.satisfiable {""} else {" not"});
            }
            println!();
            println!("TRUTH TABLE");
            println!("{}", truth_table(&phi));
            if info.tautology {
                if let Some(p) = nd::find_proof(&phi) {
                    println!("PROOF");
                    println!("{}", p);
                }
                let models = Models::new(vec![], phi);
                intu::try_find_countermodel(&models, worlds_max, &mut |worlds, w, rel, val, vars| {
                    println!("It is not an intuitionistic tautology.\n");
                    println!("COUNTERMODEL (Kripke semantics)");
                    println!("Worlds: {};", intu::fmt_worlds(worlds));
                    println!("Relation: {};", intu::fmt_relation(rel));
                    println!("Valuation: {};", intu::fmt_valuation(worlds, vars, val));
                    println!("{} does not satisfy the formula.", w);
                });
            }
        },
        Err(e) => println!("{}", e)
    }
}

fn modal_analysis_models(models: &Models, system: LogicalSystem, worlds_max: u32) {
    println!("Presented statement:\n  {}\n", models);
    modal::try_find_countermodel(models, system, worlds_max,
    &mut |worlds, w, rel, val, vars| {
        println!("COUNTERMODEL in system {system} (Kripke semantics)");
        println!("Worlds: {};", modal::fmt_worlds(worlds));
        println!("Relation: {};", modal::fmt_relation(rel));
        println!("Valuation: {};", modal::fmt_valuation(worlds, vars, val));
        println!("{} does not satisfy the formula.", w);
    });
}

fn modal_analysis(s: &str, system: LogicalSystem, worlds_max: u32) {
    match parse(s.as_bytes()) {
        Ok(phi) => {
            let AST::Prop(phi) = phi else {
                if let AST::Models(models) = phi {
                    modal_analysis_models(&models, system, worlds_max);
                }
                return;
            };
            println!("Presented formula:\n  {}\n", phi);
            let models = Models::new(vec![], phi);
            modal::try_find_countermodel(&models, system, worlds_max,
            &mut |worlds, w, rel, val, vars| {
                println!("It is not valid in system {system}.\n");
                println!("COUNTERMODEL (Kripke semantics)");
                println!("Worlds: {};", modal::fmt_worlds(worlds));
                println!("Relation: {};", modal::fmt_relation(rel));
                println!("Valuation: {};", modal::fmt_valuation(worlds, vars, val));
                println!("{} does not satisfy the formula.", w);
            });
        },
        Err(e) => println!("{}", e)
    }
}

fn main() {
    let config = match Config::from_args() {
        Ok(value) => value,
        Err(s) => {
            println!("Error: unknown system {}", s);
            return;
        }
    };
    loop {
        let s = input("> ");
        if s.is_empty() {continue;}
        match config.system {
            LogicalSystem::None => standard_analysis(&s, config.worlds_max),
            _ => modal_analysis(&s, config.system, config.worlds_max)
        }
    }
}
