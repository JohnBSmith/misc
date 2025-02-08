#!/usr/bin/env python3
from sys import argv

def chunks(a, n):
    return [a[i:i+n] for i in range(0, len(a), n)]

def generate_key():
    from random import shuffle
    key = [chr(c) for c in range(ord("a"), ord("z") + 1)]
    shuffle(key)
    return "".join(key)

def mapping_from_key(key):
    dom = [chr(c) for c in range(ord("a"), ord("z") + 1)]
    return dict(zip(dom, key))

def encode(s, key):
    s = s.lower()
    acc = []
    d = mapping_from_key(key)
    for c in s:
        if c.isalpha():
            acc.append(d[c])
    a = chunks(chunks("".join(acc), 5), 10)
    return "\n".join([" ".join(t) for t in a])

def dc_mapping_from_key(key):
    dom = [chr(c) for c in range(ord("a"), ord("z") + 1)]
    return dict(zip(key, dom))

def decode(s, key):
    s = s.lower()
    acc = []
    d = dc_mapping_from_key(key)
    for c in s:
        if c.isalpha():
            acc.append(d[c])    
    return "".join(acc)
    
def read(name):
    with open(name) as f:
        return f.read()

key = "cknbphtlfiagqsvxdyrumeowj"
plaintext = read(argv[1])
ciphertext = encode(plaintext, key)
print(ciphertext)
# print(decode(ciphertext, key))

