
use std::{io, io::Read, io::Write};
use std::fs::File;

use crate::crc32::crc;
use crate::cipher::{Keystream, ChaCha20Stream};
use crate::{
    u32_to_bytes_le, u32_from_bytes_le,
    u64_to_bytes_le, u64_from_bytes_le
};
use crate::read_exact;
use crate::assert_nonexistent;

fn write_glue_header(pfile: &mut File, ofile: &mut File,
    keystream: &mut dyn Keystream
) -> io::Result<()>
{
    let mut data: [u8;12] = [0;12];
    let len: u64 = pfile.metadata()?.len();
    data[0..8].copy_from_slice(&u64_to_bytes_le(len));
    let parity = crc(&data[0..8],0);
    data[8..12].copy_from_slice(&u32_to_bytes_le(parity));
    for _ in 0..20 {
        let mut edata: [u8;12] = data;
        keystream.encipher(&mut edata);
        ofile.write_all(&edata)?;
    }
    Ok(())
}

fn add_file(ifile: &mut File, ofile: &mut File,
    keystream: &mut dyn Keystream
) -> io::Result<()>
{
    let mut buffer: [u8;4096] = [0;4096];
    loop {
        let n = ifile.read(&mut buffer)?;
        if n == 0 {return Ok(());}
        keystream.encipher(&mut buffer[..n]);
        ofile.write_all(&buffer[..n])?;
    }
}

pub fn glue(pfile: &mut File, ifile: &mut File, ofile: &mut File,
    keystream: &mut dyn Keystream
) -> io::Result<()>
{
    write_glue_header(pfile,ofile,keystream)?;
    add_file(pfile,ofile,keystream)?;
    add_file(ifile,ofile,keystream)?;
    Ok(())
}

fn obtain_pfile_len(header: &[u8;240]) -> Result<u64,()> {
    for k in 0..20 {
        let offset = 12*k;
        let parity0 = crc(&header[offset..offset+8],0);
        let parity1 = u32_from_bytes_le(&header[offset+8..offset+12]);
        if parity0 == parity1 {
            let len = u64_from_bytes_le(&header[offset..offset+8]);
            return Ok(len);
        }
    }
    Err(())
}

fn read_to_file(count: u64, ifile: &mut File, ofile: &mut File,
    keystream: &mut dyn Keystream
) -> io::Result<()>
{
    let mut buffer: [u8;4096] = [0;4096];
    let blocks = count/4096;
    let rem = (count%4096) as usize;
    for _ in 0..blocks {
        let n = read_exact(ifile,&mut buffer)?;
        assert!(n != 0);
        keystream.encipher(&mut buffer);
        ofile.write_all(&buffer)?;
    }
    let n = read_exact(ifile,&mut buffer[..rem])?;
    assert!(n != 0);
    keystream.encipher(&mut buffer[..rem]);
    ofile.write_all(&buffer[..rem])?;
    Ok(())
}

fn input(prompt: &str) -> String {
    let mut buffer = String::new();
    print!("{}",prompt);
    io::stdout().flush().unwrap();
    io::stdin().read_line(&mut buffer).unwrap();
    buffer.pop();
    if cfg!(windows) {buffer.pop();}
    return buffer;
}

fn split4(s: &str) -> String {
    let mut rs = String::new();
    for (k, c) in s.chars().enumerate() {
        if k != 0 && k%4 == 0 {rs.push(' ');}
        rs.push(c);
    }
    return rs;
}

pub fn unglue(gfile: &mut File, pfile: &mut File, ofile: &mut File,
    keystream: &mut dyn Keystream
) -> io::Result<()>
{
    let mut header: [u8;240] = [0;240];
    let n = read_exact(gfile,&mut header)?;
    assert!(n == 240);
    keystream.encipher(&mut header);
    let len = obtain_pfile_len(&header).unwrap();
    read_to_file(len,gfile,pfile,keystream)?;
    add_file(gfile,ofile,keystream)?;
    Ok(())
}

pub fn encipher_glue(path: &str, opath: &str) -> io::Result<()> {
    assert_nonexistent(opath)?;
    let ppath = String::from(path) + ".parity";
    let ifile = &mut File::open(path)?;
    let pfile = &mut File::open(ppath)?;
    let ofile = &mut File::create(opath)?;
    let (key, mut keystream) = ChaCha20Stream::from_generated_key();
    glue(pfile,ifile,ofile,&mut keystream)?;
    println!("Key: {}",split4(&key));
    Ok(())
}

pub fn unglue_decipher(path: &str, opath: &str) -> io::Result<()> {
    let ppath = String::from(opath) + ".parity";
    assert_nonexistent(&ppath)?;
    assert_nonexistent(opath)?;
    let key = input("Key: ");
    let mut keystream = ChaCha20Stream::from_key(key);
    let gfile = &mut File::open(path)?;
    let pfile = &mut File::create(ppath)?;
    let ofile = &mut File::create(opath)?;
    unglue(gfile,pfile,ofile,&mut keystream)
}
