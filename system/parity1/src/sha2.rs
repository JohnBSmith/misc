
fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

fn ep0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

fn ep1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

fn sig0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x>>3)
}

fn sig1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x>>10)
}

static K: [u32;64] = [
	  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
	  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
	  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
	  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
	  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
	  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
	  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
	  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
];

fn transform(hasher: &mut Hasher) {
    let state = &mut hasher.state;
    let m = &mut hasher.m;
    let data = &hasher.data;
    
    let mut j = 0;
    for i in 0..16 {
        m[i] = u32::from(data[j])<<24 | (u32::from(data[j+1]) << 16) |
               u32::from(data[j+2]) << 8 | u32::from(data[j+3]);
        j += 4;
    }
    for i in 16..64 {
        m[i] = sig1(m[i - 2]).wrapping_add(m[i - 7])
            .wrapping_add(sig0(m[i - 15])).wrapping_add(m[i - 16]);
    }

    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for i in 0..64 {
        let t1 = h.wrapping_add(ep1(e)).wrapping_add(ch(e,f,g))
            .wrapping_add(K[i]).wrapping_add(m[i]);
        let t2 = ep0(a).wrapping_add(maj(a,b,c));
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

pub struct Hasher {
    state: [u32;64], data: [u8;64], m: [u32;64],
    datalen: usize, bitlen: u64
}

impl Hasher {
    pub fn new() -> Self {
        let mut hasher = Self{
            state: [0;64], data: [0;64], m: [0;64],
            datalen: 0, bitlen: 0
        };
        hasher.reset();
        return hasher;
    }

    pub fn reset(&mut self) {
        self.datalen = 0;
        self.bitlen = 0;
        self.state[0] = 0x6a09e667;
        self.state[1] = 0xbb67ae85;
        self.state[2] = 0x3c6ef372;
        self.state[3] = 0xa54ff53a;
        self.state[4] = 0x510e527f;
        self.state[5] = 0x9b05688c;
        self.state[6] = 0x1f83d9ab;
        self.state[7] = 0x5be0cd19;
    }
    
    pub fn update(&mut self, data: &[u8]) {
        for x in data {
            self.data[self.datalen] = *x;
            self.datalen += 1;
            if self.datalen == 64 {
                transform(self);
                self.bitlen += 512;
                self.datalen = 0;
            }
        }
    }
    
    pub fn finalize(&mut self, hash: &mut [u8]) {
        let mut i = self.datalen;
      
        // Pad whatever data is left in the buffer.
        if self.datalen < 56 {
            self.data[i] = 0x80;
            i += 1;
            while i < 56 {
                self.data[i] = 0x00;
                i += 1;
            }
        } else {
            self.data[i] = 0x80;
            i += 1;
            while i < 64 {
                self.data[i] = 0x00;
                i += 1;
            }
            transform(self);
            self.data[..56].copy_from_slice(&[0;56]);
        }
      
        // Append to the padding the total message's length
        // in bits and transform.
        self.bitlen += self.datalen as u64 * 8;
        self.data[63] = self.bitlen as u8;
        self.data[62] = (self.bitlen >> 8) as u8;
        self.data[61] = (self.bitlen >> 16) as u8;
        self.data[60] = (self.bitlen >> 24) as u8;
        self.data[59] = (self.bitlen >> 32) as u8;
        self.data[58] = (self.bitlen >> 40) as u8;
        self.data[57] = (self.bitlen >> 48) as u8;
        self.data[56] = (self.bitlen >> 56) as u8;
        transform(self);
      
        // Since this implementation uses little endian
        // byte ordering and SHA uses big endian,
        // reverse all the bytes when copying the final
        // state to the output hash.
        for i in 0..4 {
            hash[i]      = (self.state[0] >> (24 - i * 8)) as u8;
            hash[i + 4]  = (self.state[1] >> (24 - i * 8)) as u8;
            hash[i + 8]  = (self.state[2] >> (24 - i * 8)) as u8;
            hash[i + 12] = (self.state[3] >> (24 - i * 8)) as u8;
            hash[i + 16] = (self.state[4] >> (24 - i * 8)) as u8;
            hash[i + 20] = (self.state[5] >> (24 - i * 8)) as u8;
            hash[i + 24] = (self.state[6] >> (24 - i * 8)) as u8;
            hash[i + 28] = (self.state[7] >> (24 - i * 8)) as u8;
        }
    }
}
