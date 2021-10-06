
// Todo: Ausgabe Hashwert

use std::io;
use std::fs::File;

use crate::crc32::crc;
use crate::sha2::Hasher;
use crate::{u32_to_bytes_le, u64_to_bytes_le, u32_from_bytes_le};
use crate::{BLOCK_COUNT, BLOCK_SIZE, BUFFER_SIZE, PBLOCK_SIZE};
use crate::read_exact;
use crate::fill_zero;

pub fn data_to_string(data: &[u8]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    for x in data {
        write!(s,"{:02x}", x).unwrap();
    }
    return s;
}

struct Error {
    range: (u64, u64)
}
impl Error {
    fn print(&self) {
        println!("Error detected in {}..{}.", self.range.0, self.range.1);
    }
}

struct Checker {
    hash_data: [u8; 32],
    counter: u64,
    errors: Vec<Error>,
    errors_crypto: Vec<Error>
}

impl Checker {
    fn new() -> Self {
        Self {
            hash_data: [0; 32],
            counter: 0,
            errors: vec![],
            errors_crypto: vec![]
        }
    }
    fn check_parity_block(&mut self, buffer: &[u8], pblock: &[u8])
    -> io::Result<()>
    {
        let mut parity_crc = 0;
        for k in 0..BLOCK_COUNT {
            let value = crc(&buffer[BLOCK_SIZE*k..BLOCK_SIZE*(k+1)],0);
            parity_crc = crc(&u32_to_bytes_le(value), parity_crc);
            let value2 = u32_from_bytes_le(&pblock[4*k..4*(k+1)]);
            if value != value2 {
                let offset = self.counter*(BUFFER_SIZE as u64);
                let error = Error {range: (
                    offset + (BLOCK_SIZE*k) as u64,
                    offset + (BLOCK_SIZE*(k+1)) as u64
                )};
                error.print();
                self.errors.push(error);
            }
        }
        let mut hasher = Hasher::new();
        hasher.update(&buffer);
        hasher.finalize(&mut self.hash_data);

        parity_crc = crc(&self.hash_data, parity_crc);
        let _ = parity_crc;

        if self.hash_data != pblock[BLOCK_COUNT*4..BLOCK_COUNT*4+32] {
              let error = Error {range: (
                  self.counter*(BUFFER_SIZE as u64),
                  (self.counter+1)*(BUFFER_SIZE as u64)
              )};
              self.errors_crypto.push(error);            
        }
        self.counter += 1;
        Ok(())
    }
}

pub fn check_parity(ifile: &mut File, pfile: &mut File)
-> io::Result<()>
{
    let len: u64 = ifile.metadata()?.len();
    let mut hash: [u8;32] = [0; 32];
    let mut header: [u8;64] = [0; 64];
    let n = read_exact(pfile, &mut header)?;
    assert!(n == 64);

    let buffer: &mut [u8] = &mut [0; BUFFER_SIZE];
    let pblock: &mut [u8] = &mut [0; PBLOCK_SIZE];
    let mut checker = Checker::new();
    let mut hasher = Hasher::new();
    loop {
        let n = read_exact(ifile, buffer)?;
        if n == 0 {break;}
        hasher.update(&buffer[..n]);
        if n < BUFFER_SIZE {
            fill_zero(&mut buffer[n..]);
        }
        let n = read_exact(pfile, pblock)?;
        assert!(n == PBLOCK_SIZE);
        checker.check_parity_block(buffer, pblock)?;
    }

    let len_bytes = u64_to_bytes_le(len);
    let _len_crc = u32_to_bytes_le(crc(&len_bytes, 0));

    if !checker.errors_crypto.is_empty() {
        println!();
        println!("Encountered {} blocks with wrong CRC.",
            checker.errors.len()
        );
        println!("Encountered {} blocks with wrong cryptographic hash:",
            checker.errors_crypto.len()
        );
        for error in &checker.errors_crypto {
            error.print();
        }
        println!();
    } else {
        let value = crc(&header[12..44],0);
        let value0 = u32_from_bytes_le(&header[44..48]);
        if value == value0 {
            hasher.finalize(&mut hash);    
            assert!(hash == header[12..44]);
        } else {
            println!("Note: Parity file is damaged, but not critically.");
        }
        println!("Ok.");
        println!("SHA2-256:\n{}", data_to_string(&header[12..44]));
    }

    Ok(())
}

pub fn get_info(pfile: &mut File) -> io::Result<()> {
    let mut header: [u8; 64] = [0; 64];
    let n = read_exact(pfile, &mut header)?;
    assert!(n == 64);
    let value = crc(&header[12..44], 0);
    let value0 = u32_from_bytes_le(&header[44..48]);        
    if value == value0 {
        println!("SHA2-256:");
        println!("{}", data_to_string(&header[12..44]));
    } else {
        println!("Error: Parity file is wrong or damaged.");
    }
    Ok(())
}
