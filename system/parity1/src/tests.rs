
use crate::crc32::crc;
use crate::sha2::Hasher;
use crate::u32_to_bytes_le;

pub struct RNG {
    state: (u64,u64)
}

impl RNG {
    pub fn from_seed(seed: u64) -> Self {
        Self{state: (
            seed ^ 0xabcd1234abcd1234,
            seed ^ 0xdcba4321dcba4321
        )}
    }
    pub fn rand_u64(&mut self) -> u64 {
        let (mut x, y) = self.state;
        self.state.0 = y;
        x ^= x << 23;
        self.state.1 = x ^ y ^ (x >> 17) ^ (y >> 26);
        return self.state.1.wrapping_add(y);
    }
}

fn generate_data(seed: u64, size: usize) -> Vec<u8> {
    let mut rng = RNG::from_seed(seed);
    return (0..size).map(|_| rng.rand_u64() as u8).collect();
}

#[test]
fn test0() {
    let mut value = crc(b"",0);
    for _ in 0..10000 {
        value = crc(&u32_to_bytes_le(value),0);
    }
    assert!(value == 0xe6a94479);
}

#[test]
fn test1() {
    let data = generate_data(0,100000);
    let value = crc(&data,0);
    assert!(value == 0xd13c02df);
}

static HASH0: [u8;32] = [
    0x2c, 0x1e, 0x16, 0x90, 0x9c, 0x22, 0x0a, 0x2c,
    0x90, 0x95, 0xb8, 0xcc, 0xf2, 0x95, 0x7b, 0xf1,
    0x24, 0xf9, 0x8e, 0xdd, 0x88, 0x36, 0x9c, 0xc4,
    0x92, 0xd5, 0x35, 0x7b, 0xf1, 0xcb, 0x43, 0x66
];

#[test]
fn test2() {
    let data = generate_data(0,100000);
    let mut hasher = Hasher::new();
    hasher.update(&data);
    let mut hash: [u8;32] = [0;32];
    hasher.finalize(&mut hash);
    assert!(hash == HASH0);
}
