#!/usr/bin/env python3

# Determines the absolute frequency of n-grams in a text.
# Ermittelt die absolute Häufigkeit von n-Grammen in einem Text.

from sys import argv, exit
from collections import Counter
import re

def ngram_freq(n, text):
    # Normalize text to upper-case letters.
    # Text auf Großbuchstaben normalisieren.
    text = text.upper()

    # Remove all characters except A-Z.
    # Alle Zeichen außer A-Z entfernen.
    text = re.sub(r'[^A-Z]', '', text)

    # Count n-grams.
    # n-Gramme zählen.
    counts = Counter()
    for i in range(len(text) - (n - 1)):
        ngram = text[i:i+n]
        counts[ngram] += 1
    return counts

def main():
    try:
        with open(argv[2], 'r') as f:
            text = f.read()
    except FileNotFoundError:
        print(f"Fehler: Datei {argv[2]} nicht gefunden.")
        exit(1)

    n = int(argv[1])
    counts = ngram_freq(n, text)

    # Output: n-gram in capital letters and its absolute frequency,
    # each in one line.
    # Ausgabe: n-Gramm in Großbuchstaben und dessen absolute
    # Häufigkeit, jeweils in einer Zeile.
    by_freq = lambda t: -t[1]
    for ngram, freq in sorted(counts.items(), key = by_freq):
        print(f"{ngram} {freq}")

if __name__ == "__main__":
    main()
