
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

enum LogicalSystem {None, K}
impl LogicalSystem {
    fn from_args() -> Self {
        let argv: Vec<String> = std::env::args().collect();
        if argv.len() == 2 && argv[1] == "K" {Self::K} else {Self::None}
    }
}

fn standard_analysis_model_rel(models: &Models) {
    println!("Presented statement:\n  {}\n", models);
    intu::try_find_countermodel(&models, &mut |worlds, w, rel, val, vars| {
        println!("COUNTERMODEL (Kripke semantics)");
        println!("Worlds: {};", intu::fmt_worlds(worlds));
        println!("Relation: {};", intu::fmt_relation(rel));
        println!("Valuation: {};", intu::fmt_valuation(worlds, vars, val));
        println!("{} does not satisfy {}", w, models.prop);
    });
}

fn standard_analysis(s: &str) {
    match parse(s.as_bytes()) {
        Ok(phi) => {
            let AST::Prop(phi) = phi else {
                if let AST::Models(models) = phi {
                    standard_analysis_model_rel(&models);
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
                intu::try_find_countermodel(&models, &mut |worlds, w, rel, val, vars| {
                    println!("It is not an intuitionistic tautology.\n");
                    println!("COUNTERMODEL (Kripke semantics)");
                    println!("Worlds: {};", intu::fmt_worlds(worlds));
                    println!("Relation: {};", intu::fmt_relation(rel));
                    println!("Valuation: {};", intu::fmt_valuation(worlds, vars, val));
                    println!("{} does not satisfy {}", w, models.prop);
                });
            }
        },
        Err(e) => println!("{}", e)
    }
}

fn modal_analysis_models(models: &Models) {
    println!("Presented statement:\n  {}\n", models);
    modal::try_find_countermodel(&models, &mut |worlds, w, rel, val, vars| {
        println!("COUNTERMODEL in system K (Kripke semantics)");
        println!("Worlds: {};", modal::fmt_worlds(worlds));
        println!("Relation: {};", modal::fmt_relation(rel));
        println!("Valuation: {};", modal::fmt_valuation(worlds, vars, val));
        println!("{} does not satisfy {}", w, models.prop);
    });
}

fn modal_analysis(s: &str) {
    match parse(s.as_bytes()) {
        Ok(phi) => {
            let AST::Prop(phi) = phi else {
                if let AST::Models(models) = phi {
                    modal_analysis_models(&models);
                }
                return;
            };
            println!("Presented formula:\n  {}\n", phi);
            let models = Models::new(vec![], phi);
            modal::try_find_countermodel(&models, &mut |worlds, w, rel, val, vars| {
                println!("It is not a tautology in system K.\n");
                println!("COUNTERMODEL (Kripke semantics)");
                println!("Worlds: {};", modal::fmt_worlds(worlds));
                println!("Relation: {};", modal::fmt_relation(rel));
                println!("Valuation: {};", modal::fmt_valuation(worlds, vars, val));
                println!("{} does not satisfy {}", w, models.prop);
            });
        },
        Err(e) => println!("{}", e)
    }
}

fn main() {
    let system = LogicalSystem::from_args();
    loop {
        let s = input("> ");
        if s.is_empty() {continue;}
        match system {
            LogicalSystem::None => standard_analysis(&s),
            LogicalSystem::K => modal_analysis(&s)
        }
    }
}
