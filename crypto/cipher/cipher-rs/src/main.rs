
use std::fs::File;
use std::{io, io::Read, io::Write, io::Seek};

mod sha2;
use sha2::Hasher;

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

// ChaCha20 cipher
struct KeyStream {
    state: [u32;16],
    obuff: [u8;64],
    index: usize
}
impl KeyStream {
    fn new(key: &[u8; 32], iv: &[u8; 8]) -> Self {
        let mut state: [u32; 16] = [0; 16];
        state[0] = u32_from_bytes_le("expa".as_bytes());
        state[1] = u32_from_bytes_le("nd 3".as_bytes());
        state[2] = u32_from_bytes_le("2-by".as_bytes());
        state[3] = u32_from_bytes_le("te k".as_bytes());
        for i in 0..8 {
            state[4+i] = u32_from_bytes_le(&key[4*i..4*(i+1)]);
        }
        state[12] = 0;
        state[13] = 0;
        state[14] = u32_from_bytes_le(&iv[0..4]);
        state[15] = u32_from_bytes_le(&iv[4..8]);
        Self {state, obuff: [0; 64], index: 64}
    }
    fn next_block(&mut self) {
        let mut x: [u32; 16] = self.state;
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
    fn get(&mut self) -> u8 {
        if self.index == 64 {
            self.next_block();
            self.index = 0;
        }
        self.index += 1;
        self.obuff[self.index-1]
    } 
}

fn salt(hasher: &mut Hasher, stream: &mut KeyStream) {
    let mut buffer: [u8; 256] = [0; 256];
    for x in &mut buffer {
        *x = stream.get();
    }
    hasher.update(&buffer);
}

fn encipher(key: &[u8; 32], iv: &[u8; 8],
    ifile: &mut File, ofile: &mut File
) -> io::Result<()>
{
    let mut hash_enc: [u8; 32] = [0; 32];
    ofile.write_all(iv)?;
    ofile.write_all(&[0; 32])?;
    let mut buffer = [0; 0x10000];
    let mut stream = KeyStream::new(key, iv);
    let mut hasher = Hasher::new();
    salt(&mut hasher, &mut stream);

    for x in &mut hash_enc {
        *x = stream.get();
    }

    loop {
        let n = ifile.read(&mut buffer)?;
        if n == 0 {break;}
        hasher.update(&buffer[..n]);
        for x in &mut buffer[..n] {
            *x ^= stream.get();
        }
        ofile.write_all(&buffer[..n])?;
    }

    let mut hash: [u8; 32] = [0; 32];
    hasher.finalize(&mut hash);
    for (x, y) in hash.iter_mut().zip(&hash_enc) {
        *x ^= y;
    }
    ofile.seek(io::SeekFrom::Start(8))?;
    ofile.write_all(&hash)?;
    Ok(())
}

fn decipher(key: &[u8; 32], iv: &[u8; 8],
    ifile: &mut File, ofile: &mut File
) -> io::Result<()>
{
    let mut hash0: [u8;32] = [0;32];
    let n = ifile.read(&mut hash0)?;
    assert!(n == 32);

    let mut buffer = [0; 0x10000];
    let mut stream = KeyStream::new(key, iv);
    let mut hasher = Hasher::new();
    salt(&mut hasher, &mut stream);

    for x in &mut hash0 {
        *x ^= stream.get();
    }

    loop {
        let n = ifile.read(&mut buffer)?;
        if n == 0 {break;}
        for x in &mut buffer[..n] {
            *x ^= stream.get();
        }
        hasher.update(&buffer[..n]);
        ofile.write_all(&buffer[..n])?;
    }

    let mut hash: [u8; 32] = [0; 32];
    hasher.finalize(&mut hash);
    if hash != hash0 {
        eprintln!("\nWarning: integrity check failed or key was wrong.");
    }
    Ok(())
}

fn iter_hash_next(key: &mut [u8]) {
    let mut hasher = Hasher::new();
    hasher.update(key);
    hasher.finalize(key);
}

// Weak, but better than nothing.
fn key_stretch(key: &mut [u8]) {
    for _ in 0..10000 {
        iter_hash_next(key);
    }
}

fn key_from(salt: &[u8], mut text: String) -> [u8; 32] {
    text.retain(|c| c != ' ');
    let mut key: [u8; 32] = [0; 32];
    let mut hasher = Hasher::new();
    hasher.update(salt);
    hasher.update(text.as_bytes());
    hasher.finalize(&mut key);
    key_stretch(&mut key);
    key
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

#[cfg(windows)]
fn get_nonce() -> io::Result<[u8; 8]> {
    let text = input("(Nonce) Type in some random letters (roughly 20):\n");
    let mut buffer: [u8; 32] = [0; 32];
    let mut hasher = Hasher::new_256();
    hasher.update(text.as_bytes());
    hasher.finalize(&mut buffer);
    for _ in 10000 {
        iter_hash_next(&mut buffer);
    }
    let mut nonce = [0; 8];
    nonce.copy_from_slice(&buffer[..8]);
    Ok(nonce)
}

#[cfg(not(windows))]
fn get_nonce() -> io::Result<[u8; 8]> {
    let mut nonce: [u8; 8] = [0; 8];
    let mut rng = File::open("/dev/urandom")?;
    rng.read_exact(&mut nonce)?;
    Ok(nonce)
}

static USAGE: &str = r#"
Usage:
    Encipher: cipher -e input-file output-file
    Decipher: cipher -d input-file output-file
"#;

fn usage() {
    println!("{}", USAGE);
}

fn main() -> io::Result<()> {
    let argv: Vec<String> = std::env::args().collect();
    if argv.len() != 4 {
        usage();
        return Ok(());
    }
    if argv[1] == "-e" {
        let mut ifile = File::open(&argv[2])?;
        let mut ofile = File::create(&argv[3])?;

        let nonce = get_nonce()?;
        println!("     xxxx xxxx xxxx xxxx xxxx xxxx xxxx");
        let key = key_from(&nonce,input("Key: "));

        encipher(&key, &nonce, &mut ifile, &mut ofile)?;
    } else if argv[1] == "-d" {
        let mut ifile = File::open(&argv[2])?;
        let mut ofile = File::create(&argv[3])?;
        let mut nonce: [u8;8] = [0;8];
        let n = ifile.read(&mut nonce)?;
        assert!(n == 8);
        let key = key_from(&nonce,input("Key: "));
        decipher(&key, &nonce, &mut ifile, &mut ofile)?;
    } else {
        usage();
    }
    Ok(())
}
