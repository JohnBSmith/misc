
/*
A small tool which searches for synonyms in a given thesaurus.

This software is released under the terms of the license
Creative Commons CC0 1.0.

The used data format and main motivation is the text format export
of open source German thesaurus openthesaurus.de,
https://www.openthesaurus.de/export/OpenThesaurus-Textversion.zip
*/

use std::{io, io::Write};

struct SynonymGroups<'a> {
    list: Vec<Vec<&'a [u8]>>
}

impl SynonymGroups<'_> {
    fn find(&self, word: &str, cb: &dyn Fn(&[&[u8]])) {
        for t in &self.list {
            for s in t {
                let n = word.len();
                if n <= s.len() && word.as_bytes() == &s[..n] {
                    cb(t);
                    break;
                }
            }
        }
    }
}

fn read_input(input: &[u8]) -> SynonymGroups<'_> {
    let mut list = vec![];
    let mut t = vec![];
    let mut it = input.iter().enumerate();
    let mut j = 0;
    while let Some((i, c)) = it.next() {
        if *c == b';' {
            t.push(&input[j..i]);
            j = i + 1;
        } else if *c == b'\n' {
            t.push(&input[j..i]);
            j = i + 1;
            list.push(t.clone());
            t.clear();
        } else if *c == b'#' {
            while let Some((i, c)) = it.next() {
                if *c == b'\n' {j = i + 1; break;}
            }
        }
    }
    SynonymGroups {list}
}

fn print_group(t: &[&[u8]]) {
    for item in t {
        let _ = io::stdout().write_all(item);
        println!();
    }
}

fn input(prompt: &str) -> String {
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

fn process_word(word: &str, groups: &SynonymGroups) {
    groups.find(word, &|t| {
        print_group(t);
        println!();
    });
}

fn data_path() -> std::path::PathBuf {
    const PATH: &str = ".local/share/data/thesaurus.txt";
    let home_path = std::env::var("HOME").unwrap();
    [&home_path, PATH].iter().collect()
}

fn main() {
    let path = data_path();
    let data = match std::fs::read(&path) {
        Ok(data) => data,
        Err(e) => {
            let path = path.to_str().unwrap_or("INVALID UNICODE");
            eprintln!("Could not read '{}'.", path);
            println!("{}", e);
            return;
        }
    };
    let groups = read_input(&data);
    loop {
        let word = input("> ");
        if word.len() > 1 {
            process_word(&word, &groups);
        }
    }
}
