
use std::{io, io::Read, io::Write, io::Seek};
use std::fs::File;
use std::path::Path;

mod crc32;
mod sha2;
mod check;

use crc32::crc;
use sha2::Hasher;

#[cfg(test)]
mod tests;

const BLOCK_SIZE: usize = 256;
const BLOCK_COUNT: usize = 64;
const BUFFER_SIZE: usize = BLOCK_SIZE*BLOCK_COUNT;
const PBLOCK_SIZE: usize = BLOCK_COUNT*4 + 32 + 4;

fn read_exact(file: &mut impl Read, mut buffer: &mut [u8])
-> io::Result<usize>
{
    let mut sum = 0;
    while !buffer.is_empty() {
        let n = file.read(&mut buffer)?;
        if n == 0 {break;}
        buffer = &mut buffer[n..];
        sum += n;
    }
    return Ok(sum);
}

fn fill_zero(a: &mut [u8]) {
    for x in a {*x = 0;}
}

fn u32_from_bytes_le(a: &[u8]) -> u32 {
    u32::from(a[0]) | u32::from(a[1])<<8 |
    u32::from(a[2])<<16 | u32::from(a[3])<<24
}

fn u32_to_bytes_le(x: u32) -> [u8;4] {
    [x as u8, (x>>8) as u8, (x>>16) as u8, (x>>24) as u8]
}

fn u64_to_bytes_le(x: u64) -> [u8;8] {
    [x as u8, (x>>8) as u8, (x>>16) as u8, (x>>24) as u8,
    (x>>32) as u8, (x>>40) as u8, (x>>48) as u8, (x>>56) as u8]
}

struct Generator {
    hash_data: [u8;32]
}

impl Generator {
    fn new() -> Self {
        Self {hash_data: [0;32]}
    }
    fn generate_parity_block(&mut self, buffer: &[u8], ofile: &mut File)
    -> io::Result<()>
    {
        let mut parity_crc = 0;
        for k in 0..BLOCK_COUNT {
            let value = u32_to_bytes_le(crc(&buffer[BLOCK_SIZE*k..BLOCK_SIZE*(k+1)],0));
            parity_crc = crc(&value,parity_crc);
            ofile.write_all(&value)?;
        }
        let mut hasher = Hasher::new();
        hasher.update(&buffer);
        hasher.finalize(&mut self.hash_data);

        parity_crc = crc(&self.hash_data,parity_crc);
        ofile.write_all(&self.hash_data)?;
        ofile.write_all(&u32_to_bytes_le(parity_crc))?;
        Ok(())
    }
}

fn generate_parity(ifile: &mut File, ofile: &mut File)
-> io::Result<()>
{
    let len: u64 = ifile.metadata()?.len();
    let mut header: [u8;64] = [0;64];
    ofile.write_all(&header)?;
    let buffer: &mut [u8] = &mut [0; BUFFER_SIZE];
    let mut gen = Generator::new();
    let mut hasher = Hasher::new();
    loop {
        let n = read_exact(ifile,buffer)?;
        if n == 0 {break;}
        hasher.update(&buffer[..n]);
        if n < BUFFER_SIZE {
            fill_zero(&mut buffer[n..]);
        }
        gen.generate_parity_block(buffer,ofile)?;
    }
    
    header[0..12].copy_from_slice(b"\x00\x00parity001:");
    hasher.finalize(&mut header[12..44]);
    let value = u32_to_bytes_le(crc(&mut header[12..44],0));
    header[44..48].copy_from_slice(&value);

    let len_bytes = u64_to_bytes_le(len);
    let len_crc = u32_to_bytes_le(crc(&len_bytes,0));
    header[48..56].copy_from_slice(&len_bytes);
    header[56..60].copy_from_slice(&len_crc);

    header[60..64].copy_from_slice(b"----");

    ofile.seek(io::SeekFrom::Start(0))?;
    ofile.write_all(&header)?;
    Ok(())
}

fn is_option(arg: &str) -> bool {
    !arg.is_empty() && &arg[0..1] == "-"
}

static HELP_MESSAGE: &str = r#"
Usage
-----

parity FILE
    Generates 'FILE.parity'.

parity FILE FILE.parity
    Checks the integrity.

parity -i FILE.parity
    Reads out the SHA2-256 hash value of 'FILE.parity'.
"#;

fn main() -> io::Result<()> {
    let argv: Vec<String> = std::env::args().collect();
    if argv.len()<2 {
        println!("{}",HELP_MESSAGE);
    } else if is_option(&argv[1]) {
        if argv[1]=="-i" && argv.len()==3 {
            let pfile = &mut File::open(&argv[2])?;
            check::get_info(pfile)?;
        } else {
            println!("{}",HELP_MESSAGE);                
        }
    } else if argv.len()==2 {
        let opath = argv[1].clone() + ".parity";
        if Path::new(&opath).exists() {
            return Err(io::Error::new(io::ErrorKind::AlreadyExists,
                format!("Path '{}' already exists.",&opath)));
        }
        let ifile = &mut File::open(&argv[1])?;
        let ofile = &mut File::create(opath)?;
        generate_parity(ifile,ofile)?;
    } else if argv.len()==3 {
        let ifile = &mut File::open(&argv[1])?;
        let pfile = &mut File::open(&argv[2])?;
        check::check_parity(ifile,pfile)?;
    } else {
        println!("{}",HELP_MESSAGE);
    }
    Ok(())
}
