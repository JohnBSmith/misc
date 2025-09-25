
use std::collections::{HashSet, HashMap};

static FMT_TAB: &[(&str, &str)] = &[
    ("&", "∧"), ("~", "¬"), ("->", "→"), ("=>", "→"), ("/\\", "∧"), ("\\/", "∨"),
    ("|-", "⊢"), ("<->", "↔"), ("<=>", "↔"), ("*", "⋅"), ("<=", "≤")
];
static FMT_KW_TAB: &[(&str, &str)] = &[
    ("and", "∧"), ("or", "∨"), ("not", "¬"), ("false", "⊥"), ("true", "⊤"),
    ("box", "□"), ("dia", "◇"), ("forall", "∀"), ("exists", "∃"), ("in", "∈"),
    ("sub", "⊆"), ("cup", "∪"), ("cap", "∩"), ("Cap", "⋂"), ("Cup", "⋃"),
    ("times", "×"), ("empty_set", "∅"), ("circ", "∘"), ("equiv", "≡"),
    ("phi", "φ"), ("psi", "ψ"), ("chi", "χ")
];
static UNSPACE_SET: &[&str] = &[
    "not", "box", "dia", "forall", "exists", "Cap", "Cup"
];

fn new_fmt_tab<'a>(tab: &[(&'a str, &'a str)]) -> HashMap<&'a [u8], &'a [u8]> {
    let mut m = HashMap::new();
    for (key, value) in tab {
        m.insert(key.as_bytes(), value.as_bytes());
    }
    m
}

fn new_unspace_set() -> HashSet<&'static [u8]> {
    let mut s = HashSet::new();
    for x in UNSPACE_SET {
        s.insert(x.as_bytes());
    }
    s
}

pub fn format_source_code(s: &[u8]) -> Vec<u8> {
    let fmt_tab = new_fmt_tab(FMT_TAB);
    let fmt_kw_tab = new_fmt_tab(FMT_KW_TAB);
    let unspace_set = new_unspace_set();
    let mut i = 0;
    let n = s.len();
    let mut acc: Vec<u8> =Vec::with_capacity(n);
    while i < n {
        let mut fmt = false;
        for k in [3, 2, 1] {
            if i + k - 1 < n {
                if let Some(x) = fmt_tab.get(&s[i..i+k]) {
                    acc.extend(x.iter());
                    i += k; fmt = true; break;
                }
            }
        }
        if !fmt {
            if s[i].is_ascii_alphabetic() || s[i] == b'_' {
                let j = i;
                while i < n && (s[i].is_ascii_alphabetic() ||
                    s[i].is_ascii_digit() || s[i] == b'_' || s[i] == b'\''
                ) {
                    i += 1;
                }
                let sji = &s[j..i];
                acc.extend(match fmt_kw_tab.get(sji) {
                    Some(sf) => sf,
                    None => sji
                }.iter());
                if unspace_set.contains(sji) && i < n && s[i] == b' ' {
                    i += 1;
                }
            } else if s[i] == b'#' {
                while s[i] != b'\n' {
                    acc.push(s[i]);
                    i += 1;
                }
            }else if s[i] == b'(' && i + 1 < n && s[i+1] == b'*' {
                while i + 1 < n && (s[i] != b'*' || s[i+1] != b')') {
                    acc.push(s[i]);
                    i += 1;
                }
                acc.extend(s[i..i+2].iter());
                i += 2;
            } else {
                acc.push(s[i]);
                i += 1;
            }
        }
    }
    acc
}
