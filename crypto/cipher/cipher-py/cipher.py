#!/usr/bin/python3

# Usage:
# Encipher: python3 cipher.py -e input-file output-file
# Decipher: python3 cipher.py -d input-file output-file

import os, hashlib, struct
from sys import argv, exit

# ChaCha20 Cipher
def keystream(key, iv, position=0):
    assert isinstance(key,bytes) and len(key)==32
    assert isinstance(iv, bytes) and len(iv)==8

    def rotate(v, c):
        return ((v << c) & 0xffffffff) | v >> (32 - c)

    def quarter_round(x, a, b, c, d):
        x[a] = (x[a] + x[b]) & 0xffffffff
        x[d] = rotate(x[d] ^ x[a], 16)
        x[c] = (x[c] + x[d]) & 0xffffffff
        x[b] = rotate(x[b] ^ x[c], 12)
        x[a] = (x[a] + x[b]) & 0xffffffff
        x[d] = rotate(x[d] ^ x[a], 8)
        x[c] = (x[c] + x[d]) & 0xffffffff
        x[b] = rotate(x[b] ^ x[c], 7)

    ctx = [0] * 16
    ctx[:4] = (1634760805, 857760878, 2036477234, 1797285236)
    ctx[4 : 12] = struct.unpack('<8L', key)
    ctx[12] = ctx[13] = position
    ctx[14 : 16] = struct.unpack('<LL', iv)
    while 1:
        x = list(ctx)
        for i in range(10):
            quarter_round(x, 0, 4,  8, 12)
            quarter_round(x, 1, 5,  9, 13)
            quarter_round(x, 2, 6, 10, 14)
            quarter_round(x, 3, 7, 11, 15)
            quarter_round(x, 0, 5, 10, 15)
            quarter_round(x, 1, 6, 11, 12)
            quarter_round(x, 2, 7,  8, 13)
            quarter_round(x, 3, 4,  9, 14)
        for c in struct.pack('<16L', *(
            (x[i] + ctx[i]) & 0xffffffff for i in range(16))):
            yield c
        ctx[12] = (ctx[12] + 1) & 0xffffffff
        if ctx[12] == 0:
            ctx[13] = (ctx[13] + 1) & 0xffffffff

def apply_xor(stream, data):
    assert isinstance(data, bytes)
    return bytes(x^y for x, y in zip(data, stream))

def hash_value(*a):
    hasher = hashlib.sha256()
    for data in a:
        hasher.update(data)
    return hasher.digest()

# Weak, but better than nothing.
def key_stretch(h):
    for k in range(10000): h = hash_value(h)
    return h

def key_hash(salt, key):
    h = hash_value(salt + key.replace(" ", "").encode("utf-8"))
    return key_stretch(h)

def encipher(ipath,opath):
    iv = os.urandom(8)
    print("     xxxx xxxx xxxx xxxx xxxx xxxx xxxx")
    key = key_hash(iv, input("Key: "))
    with open(ipath, 'rb') as plain:
        data = plain.read()
        stream = keystream(key, iv)
        salt = bytes(next(stream) for i in range(256))
        edata = apply_xor(stream, hash_value(salt, data) + data)
    with open(opath, 'wb') as out:
        out.write(iv)
        out.write(edata)

def decipher(ipath, opath):
    with open(ipath, 'rb') as chiff:
        iv = chiff.read(8)
        key = key_hash(iv, input("Key: "))
        edata = chiff.read()
        stream = keystream(key, iv)
        salt = bytes(next(stream) for i in range(256))
        data = apply_xor(stream, edata)
        h, data = data[:32], data[32:]
        if h != hash_value(salt, data):
            print("Warning: key is wrong or data was corrupted.\n")
    with open(opath, 'wb') as out:
        out.write(data)

def usage():
    print("\nUsage: cipher.py (-e|-d) input-file output-file\n")
    exit(1)

def main():
    if len(argv) != 4: usage()
    mode, ipath, opath = argv[1:]
    if mode == "-e":
        encipher(ipath, opath)
    elif mode == "-d":
        decipher(ipath, opath)
    else:
        usage()

main()
