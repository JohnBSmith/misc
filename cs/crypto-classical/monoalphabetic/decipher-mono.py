#!/usr/bin/env python3

# This program deciphers monoalphabetic substitutions of the 26 letters
# of the Latin alphabet by means of frequency analysis with respect to
# tetragrams. It evaluates potential plaintexts using a score function.
# By means of hill climbing with simulated annealing, it finds a key
# that maximizes the score. In each iteration step, the key is changed
# randomly by transposing two letters, which is adopted if the score
# improves.

# Dieses Programm entschlüsselt monoalphabetische Substitutionen der 26
# Buchstaben des lateinischen Alphabets vermittels Häufigkeitsanalyse
# bezüglich Tetragrammen. Es bewertet potentielle Klartexte anhand
# einer Score-Funktion. Vermittels Hill-Climbing mit Simulated Annealing
# findet es so einen Schlüssel, der den Score maximiert. Hierbei findet
# in jedem Iterationsschritt eine zufällige Änderung des Schlüssels
# per Transposition zweier Buchstaben statt, die übernommen wird, sofern
# sich der Score verbessert.

from math import exp, log
from sys import argv
import random

AZ = "abcdefghijklmnopqrstuvwxyz"

class Scorer:
    # Loads the tetragram frequencies from a file and calculates the
    # score value for each tetragram.
    # Lädt die Tetragramm-Häufigkeiten aus einer Datei und berechnet
    # daraus zu jedem Tetragramm den Score-Wert.
    def __init__(self, filename):
        self.tetragrams = {}
        with open(filename, 'r') as f:
            for line in f:
                parts = line.split()
                if len(parts) != 2:
                    continue
                tetra, count = parts[0], int(parts[1])
                self.tetragrams[tetra.lower()] = count
        self.N = sum(self.tetragrams.values())
        # Calculate the logarithmic probabilities.
        # Logwahrscheinlichkeiten berechnen.
        for tetra in self.tetragrams:
            value = log(float(self.tetragrams[tetra])/self.N)
            self.tetragrams[tetra] = value
        # If a tetragram is not found, use a minimum score.
        # Falls ein Tetragramm nicht gefunden wird, verwende einen
        # minimalen Score.
        self.floor = log(0.01/self.N)

    # A method for evaluating how English a text looks.
    # Eine Methode zur Bewertung, wie englisch ein Text ausschaut.
    def score(self, text):
        score = 0
        for i in range(len(text) - 3):
            tetra = text[i:i+4]
            score += self.tetragrams.get(tetra, self.floor)
        return score/(len(text) - 3)

def decrypt(ciphertext, key):
    mapping = dict(zip(AZ, key))
    return "".join(mapping.get(c, c) for c in ciphertext)

def random_key():
    letters = list(AZ)
    random.shuffle(letters)
    return "".join(letters)

# Tries to find the right key by hill climbing.
# Versucht, mittels Hill-Climbing den passenden Schlüssel zu finden.
def hill_climb(start_key, ciphertext, scorer, iterations=10000):
    key = start_key
    plain = decrypt(ciphertext, key)
    score = scorer.score(plain)
    best_score = score
    best_key = key
    T = 0.1 # Temperature

    for _ in range(iterations):
        # Create a candidate by randomly swapping two letters in the key.
        # Erzeuge einen Kandidaten durch zufälligen Tausch zweier
        # Buchstaben im Schlüssel.
        key_list = list(key)
        i, j = random.sample(range(26), 2)
        key_list[i], key_list[j] = key_list[j], key_list[i]
        candidate_key = "".join(key_list)
        plain = decrypt(ciphertext, candidate_key)
        candidate_score = scorer.score(plain)

        # Accept the new key when the score increases or, with a certain
        # probability, when the score deteriorates (simulated annealing)
        # in order to escape from small local maxima.
        # Akzeptiere den neuen Schlüssel, wenn der Score steigt oder
        # mit einer gewissen Wahrscheinlichkeit auch bei Score-
        # Verschlechterung (Simulated Annealing), um aus kleinen
        # lokalen Maxima zu entkommen.
        delta = candidate_score - score
        if delta > 0 or exp(delta/T) > random.random():
            key = candidate_key
            score = candidate_score
            if score > best_score:
                best_score = score
                best_key = key
    return best_key, best_score

def read_all(path):
    with open(path, 'r') as f:
        text = f.read()
        return "".join(text.strip().split()).lower()
        
# Make sure that the file "english-tetragrams.txt" is in the same
# directory in which the program is called. It contains the absolute
# frequencies of the tetragrams in a text corpus of the English
# language. The format is:
# THAT 1151
# THER 761
# NTHE 719
# HERE 617
# The listed frequencies were generated with ngram-freq.py from
# "The Hound of the Baskervilles".

# Man stelle sicher, dass die Datei "english-tetragrams.txt" im selben
# Verzeichnis liegt, in dem das Programm aufgerufen wird. Diese enthält
# die absoluten Häufigkeiten der Tetragramme in einem Textkorpus der
# englischen Sprache.

def main():
    ciphertext = read_all(argv[1])
    scorer = Scorer("english-tetragrams.txt")

    print("Entschlüsselung wird durchgeführt ...")
    key = random_key()
    iterations = 10000
    best_key, _ = hill_climb(key, ciphertext, scorer, iterations)
    plaintext = decrypt(ciphertext, best_key)

    print("\nGefundener Schlüssel:")
    print(AZ)
    print(best_key)
    print("\nDechiffrierter Text:")
    print(plaintext)

if __name__ == '__main__':
    main()
