
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, BufRead};
use tiny_rng::{Rng, Rand};

static AZ: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
const LEN: usize = 26;

struct Scorer {
    tetragrams: HashMap<[u8; 4], f64>,
    floor: f64,
}

fn error_in_line(i: usize, filename: &str) -> ! {
    panic!("Datei '{}' scheint in Zeile {} fehlerhaft zu sein.",
        filename, i + 1)
}

impl Scorer {
    fn new(filename: &str) -> Self {
        let mut tetragrams: HashMap<[u8; 4], f64> = HashMap::new();

        let Ok(file) = File::open(filename) else {
            panic!("Konnte die Datei '{}' nicht öffnen.", filename)
        };
        let reader = BufReader::new(file);
        let mut total: u32 = 0;
        for (i, line) in reader.lines().enumerate() {
            let Ok(l) = line else {error_in_line(i, filename)};
            let parts: Vec<&str> = l.split_whitespace().collect();
            if parts.len() != 2 {error_in_line(i, filename);}
            let tetra = parts[0].to_lowercase();
            let tetra_u8: [u8; 4] = tetra.as_bytes().try_into().unwrap();
            if let Ok(count) = parts[1].parse::<u32>() {
                tetragrams.insert(tetra_u8, f64::from(count));
                total += count;
            } else {
                error_in_line(i, filename)
            }
        }
        let total_f = total as f64;
        for value in tetragrams.values_mut() {
            *value = f64::ln(*value / total_f);
        }
        let floor = f64::ln(0.01 / total_f);
        Scorer {tetragrams, floor}
    }

    fn score(&self, text: &[u8]) -> f64 {
        let mut score = 0.0;
        if text.len() < 4 {return score;}
        for i in 0..text.len() - 3 {
            let tetra: [u8; 4] = text[i..i + 4].try_into().unwrap();
            score += *self.tetragrams.get(&tetra).unwrap_or(&self.floor);
        }
        score/((text.len() - 3) as f64)
    }
}

fn decrypt(key: &[u8], ciphertext: &[u8], plain: &mut[u8]) {
    for (i, &byte) in ciphertext.iter().enumerate() {
        plain[i] = if byte >= b'a' && byte <= b'z' {
            key[(byte - b'a') as usize]
        } else {
            byte
        };
    }
}

fn random_key(rng: &mut Rng) -> Vec<u8> {
    let mut letters: Vec<u8> = AZ.to_vec();
    rng.shuffle(&mut letters);
    letters
}

fn hill_climb(rng: &mut Rng, mut key: Vec<u8>, ciphertext: &[u8],
    scorer: &Scorer, max_iterations: u32
) -> (f64, Vec<u8>)
{
    let mut plain: Vec<u8> = vec![0; ciphertext.len()];
    decrypt(&key, ciphertext, &mut plain);
    let mut score = scorer.score(&plain);
    let mut best_score = score;
    let mut best_key = key.clone();
    let temp = 0.1;

    for _ in 0..max_iterations {
        let mut candidate_key = key.clone();
        let i = rng.rand_bounded_usize(LEN);
        let mut j = rng.rand_bounded_usize(LEN);
        while j == i {
            j = rng.rand_bounded_usize(LEN);
        }
        candidate_key.swap(i, j);
        decrypt(&candidate_key, ciphertext, &mut plain);
        let candidate_score = scorer.score(&plain);

        if candidate_score > score ||
        f64::exp((candidate_score - score)/temp) > rng.rand_f64() {
            key = candidate_key;
            score = candidate_score;
            if score > best_score {
                best_score = score;
                best_key = key.clone();
            }
        }
    }
    (best_score, best_key)
}

fn hill_climb_multi(rng: &mut Rng, ciphertext: &[u8],
    scorer: &Scorer, multi: u32, max_iter: u32
) -> (Vec<u8>, Vec<u8>) {
    let mut best_score = -f64::INFINITY;
    let mut best_key: Vec<u8> = AZ.to_vec();
    for _ in 0..multi {
        let start_key = random_key(rng);
        let (score, key) = hill_climb(rng, start_key, ciphertext,
            &scorer, max_iter);
        if score > best_score {
            best_score = score;
            best_key = key;
        }
    }
    let mut plain: Vec<u8> = vec![0; ciphertext.len()];
    decrypt(&best_key, ciphertext, &mut plain);
    (best_key, plain)
}

fn read_ciphertext(path: &str) -> std::io::Result<String> {
    let mut s = std::fs::read_to_string(path)?;
    s.retain(|c| !c.is_whitespace());
    Ok(s)
}

fn main() -> std::io::Result<()> {
    let argv: Vec<String> = std::env::args().collect();
    let Ok(ciphertext) = read_ciphertext(&argv[1]) else {
        println!("Konnte die Datei {} nicht öffnen.", &argv[1]);
        return Ok(());
    };
    let seed: u64 = if argv.len() > 2 {
        argv[2].parse::<u64>().expect("argv[2] muss eine Zahl sein")
    } else {0};
    let multi: u32 = if argv.len() > 3 {
        argv[3].parse::<u32>().expect("argv[3] muss eine Zahl sein")
    } else {1};
    let max_iter: u32 = if argv.len() > 4 {
        argv[4].parse::<u32>().expect("argv[4] muss eine Zahl sein")
    } else {10000};

    let scorer = Scorer::new("english-tetragrams.txt");
    let mut rng = Rng::from_seed(seed);

    println!("Entschlüsselung wird durchgeführt ...");
    let (best_key, plain) = hill_climb_multi(&mut rng,
        ciphertext.as_bytes(), &scorer, multi, max_iter);

    let key_str = String::from_utf8(best_key).unwrap();
    let plaintext = String::from_utf8(plain).unwrap();

    println!("\nGefundener Schlüssel:");
    println!("{}", key_str);
    println!("\nDechiffrierter Text:");
    println!("{}", plaintext);

    Ok(())
}
