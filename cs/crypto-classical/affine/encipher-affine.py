#!/usr/bin/env python3
from sys import argv

# Verschlüsselt Texte mit der affinen Chiffre, einem klassischen,
# ausgesprochen unsicheren Verfahren. Typische Parameter sind a = 1
# für die Caesar-Chiffre, speziell a = 1, b = 13 für die selbstinverse
# Chiffre ROT13.
#
# ANWENDUNG
#
# Zur Verschlüsselung:
#     encipher-affine.py a b -e plaintext.txt
#
# Zur Entschlüsselung:
#     encipher-affine.py a b -d ciphertext.txt

# Berechnet das multiplikative Inverse von a zum Modul m
# mithilfe des erweiterten euklidischen Algorithmus.
# Voraussetzung:
#     a und m müssen teilerfremd sein, das heißt, ggT(a, m) = 1.
def mod_inverse(a, m):
    if m == 1: return 0
    m0 = m
    x0, x1 = 0, 1
    while m != 0:
        q = a//m
        a, m = m, a%m
        x0, x1 = x1 - q*x0, x0
    if a != 1:
        raise ValueError("a und m sind nicht teilerfremd")
    return x1%m0

class AffineCipher:
    def __init__(self, a, b, alphabet):
        self.a = a
        self.b = b
        self.alphabet = alphabet

    def normalize(self, text):
        return "".join(c for c in text if c in self.alphabet)

    def encipher(self, text):
        a = self.a; b = self.b; alphabet = self.alphabet
        m = len(alphabet)
        encode = dict((y, x) for (x, y) in enumerate(alphabet))
        decode = dict((x, y) for (x, y) in enumerate(alphabet))
        return "".join(decode[(a*encode[c] + b)%m] for c in text)
        
    def decipher(self, text):
        a = self.a; b = self.b; alphabet = self.alphabet
        m = len(alphabet); ainv = mod_inverse(a, m)
        encode = dict((y, x) for (x, y) in enumerate(alphabet))
        decode = dict((x, y) for (x, y) in enumerate(alphabet))
        return "".join(decode[(ainv*(encode[c] - b))%m] for c in text)

def main():
    AZ = "abcdefghijklmnopqrstuvwxyz"
    a = int(argv[1])
    b = int(argv[2])
    cipher = AffineCipher(a, b, AZ)
    with open(argv[4], "r") as f:
        text = f.read()
    if argv[3] == "-e":
        plaintext = cipher.normalize(text.lower())
        ciphertext = cipher.encipher(plaintext)
        print(ciphertext)
    elif argv[3] == "-d":
        ciphertext = cipher.normalize(text.lower())
        plaintext = cipher.decipher(ciphertext)
        print(plaintext)

if __name__ == '__main__':
    main()
