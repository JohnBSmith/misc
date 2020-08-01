
"""
from zlib import crc32
import struct

def u32_as_bytes_le(x):
    return struct.pack("I",x)

value = crc32(b"",0)
for i in range(0,10000):
    value = crc32(u32_as_bytes_le(value),0)

print("{:08x}".format(value))
"""

# Xorshift+
def rng(seed):
    s0 = seed ^ 0xabcd1234abcd1234
    s1 = seed ^ 0xdcba4321dcba4321
    def rand():
        nonlocal s0, s1
        x, y = s0, s1
        x = x ^ ((x << 23) & 0xffffffffffffffff)
        x = (x ^ (x >> 17)) ^ (y ^ (y >> 26))
        s0, s1 = y, x
        return (s0 + s1) & 0xffffffffffffffff
    return rand

def generate_data(seed,size):
    rand = rng(seed)
    return bytes(rand() & 0xff for k in range(size))

from zlib import crc32
from hashlib import sha256

data = generate_data(0,100000)
# value = crc32(data,0)
# print("{:08x}".format(value))

print(sha256(data).hexdigest())




