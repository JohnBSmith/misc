
use std::fs::File;
use std::io::Read;
use crate::sha2::Hasher;

static IV_NONE: &[u8;8] = b"12345678";

pub trait Keystream {
    fn encipher(&mut self, data: &mut [u8]);
}

pub struct KeystreamNone;
impl Keystream for KeystreamNone {
    fn encipher(&mut self, _data: &mut [u8]) {}
}

fn u32_from_bytes_le(a: &[u8]) -> u32 {
    u32::from(a[0]) | u32::from(a[1])<<8 |
    u32::from(a[2])<<16 | u32::from(a[3])<<24
}

fn quarter_round(x: &mut [u32;16],
    a: usize, b: usize, c: usize, d: usize
) {
    x[a] = x[a].wrapping_add(x[b]);
    x[d] = (x[d]^x[a]).rotate_left(16);
    x[c] = x[c].wrapping_add(x[d]);
    x[b] = (x[b]^x[c]).rotate_left(12);
    x[a] = x[a].wrapping_add(x[b]);
    x[d] = (x[d]^x[a]).rotate_left(8);
    x[c] = x[c].wrapping_add(x[d]);
    x[b] = (x[b]^x[c]).rotate_left(7);
}

pub struct ChaCha20Stream {
    state: [u32;16],
    obuff: [u8;64],
    index: usize
}
impl ChaCha20Stream {
    fn new(key: &[u8;32], iv: &[u8;8]) -> Self {
        let mut state: [u32;16] = [0;16];
        state[0] = u32_from_bytes_le("expa".as_bytes());
        state[1] = u32_from_bytes_le("nd 3".as_bytes());
        state[2] = u32_from_bytes_le("2-by".as_bytes());
        state[3] = u32_from_bytes_le("te k".as_bytes());
        for i in 0..8 {
            state[4+i] = u32_from_bytes_le(&key[4*i..4*(i+1)]);
        }
        state[12] = 0; // Counter, niederwertige Bits
        state[13] = 0; // Counter, höherwertige Bits
        state[14] = u32_from_bytes_le(&iv[0..4]);
        state[15] = u32_from_bytes_le(&iv[4..8]);
        return Self{state, obuff: [0;64], index: 64};
    }
    fn next_block(&mut self) {
        let mut x: [u32;16] = self.state;
        for _ in 0..10 {
            quarter_round(&mut x, 0, 4,  8, 12);
            quarter_round(&mut x, 1, 5,  9, 13);
            quarter_round(&mut x, 2, 6, 10, 14);
            quarter_round(&mut x, 3, 7, 11, 15);
            quarter_round(&mut x, 0, 5, 10, 15);
            quarter_round(&mut x, 1, 6, 11, 12);
            quarter_round(&mut x, 2, 7,  8, 13);
            quarter_round(&mut x, 3, 4,  9, 14);
        }
        for i in 0..16 {
            let value = self.state[i].wrapping_add(x[i]);
            self.obuff[4*i] = value as u8;
            self.obuff[4*i+1] = (value>>8) as u8;
            self.obuff[4*i+2] = (value>>16) as u8;
            self.obuff[4*i+3] = (value>>24) as u8;
        }
        self.state[12] = self.state[12].wrapping_add(1);
        if self.state[12] == 0 {self.state[13] += 1;}
    }
    pub fn from_generated_key() -> (String,Self) {
        let key_string = generate_key();
        let key = key_from(key_string.clone());
        (key_string,ChaCha20Stream::new(&key,IV_NONE))
    }
    pub fn from_key(key_string: String) -> Self {
        let key = key_from(key_string);
        ChaCha20Stream::new(&key,IV_NONE)
    }
}

impl Keystream for ChaCha20Stream {
    fn encipher(&mut self, data: &mut [u8]) {
        for x in data {
            if self.index == 64 {
                self.next_block();
                self.index = 0;
            }
            *x ^= self.obuff[self.index];
            self.index += 1;
        }
    }
}

fn iter_hash_next(key: &mut [u8]) {
    let mut hasher = Hasher::new();
    hasher.update(key);
    hasher.finalize(key);
}

fn key_from(mut text: String) -> [u8;32] {
    text.retain(|c| c != ' ');
    let mut key: [u8;32] = [0;32];
    let mut hasher = Hasher::new();
    hasher.update(text.as_bytes());
    hasher.finalize(&mut key);
    for _ in 0..10000 {
        iter_hash_next(&mut key);
    }
    return key;
}

static ALPHABET: &[u8] =
    b"0123456789abcdefghijklmnopqrstuvwxyz";

pub fn generate_key() -> String {
    let mut bytes = File::open("/dev/urandom")
        .expect("Could not open /dev/urandom.").bytes();
    let mut key = String::new();
    while key.len() < 28 {
        let byte: u8 = bytes.next().unwrap().unwrap();
        let k = usize::from(byte % 64);
        if k<ALPHABET.len() {
            key.push(char::from(ALPHABET[k]));
        }
    }
    return key;
}

