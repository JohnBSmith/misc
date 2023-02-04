
mod parser;
pub mod comb;
mod nd;

mod classical;
mod intu;

#[cfg(test)]
mod test;

use parser::parse;
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

fn main() {
    loop {
        let s = input("> ");
        if s.is_empty() {continue;}
        match parse(s.as_bytes()) {
            Ok(phi) => {
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
                    intu::try_find_countermodel(&phi, &mut |worlds, w, rel, val, vars| {
                        println!("It is not an intuitionistic tautology.\n");
                        println!("COUNTERMODEL (Kripke semantics)");
                        println!("Worlds: {};", intu::fmt_worlds(worlds));
                        println!("Relation: {};", intu::fmt_relation(rel));
                        println!("Valuation: {};", intu::fmt_valuation(worlds, vars, val));
                        println!("{} does not satisfy {}", w, phi);
                    });
                }
            },
            Err(e) => println!("{}", e)
        }
    }
}
