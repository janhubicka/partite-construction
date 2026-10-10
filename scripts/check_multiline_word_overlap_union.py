#!/usr/bin/env python3
"""Exact two-coordinate native Hales--Jewett overlap regression.

A is the two-vertex edge on parts {0,1}. B has two disjoint copies of
that edge indexed 0 and 1, and B's part map forgets the copy index.
The two letters e_0,e_1 are induced partite copies of A in B.

Three genuine native lines have variable-coordinate sets {0},{1},{1}.
Their two pairwise overlaps with the first line each occupy a SINGLE
word A-copy, as proved abstractly in ClosureDisjointLineOverlap.lean.
The UNION of these overlaps has four vertices but every A-word copy
has two vertices: NO one word A-copy contains the whole separator.
"""
from itertools import product

PARTS = (0, 1)
COPIES = (0, 1)
VERTICES = tuple(product(PARTS, COPIES))


def embed(letter, part):
    return (part, letter)


def part(vertex):
    return vertex[0]


def edge_A(p, q):
    return p != q


def edge_B(x, y):
    return part(x) != part(y) and x[1] == y[1]


def line_map(symbols, x):
    return tuple(x if sym is None else embed(sym, part(x)) for sym in symbols)


def line_image(symbols):
    return {line_map(symbols, x) for x in VERTICES}


def edge_power(x, y):
    return all(edge_B(u, v) for u, v in zip(x, y))


def word_image(letters):
    return {tuple(embed(letters[k], p) for k in range(2)) for p in PARTS}


def check():
    # The letters and all word maps are ACTUAL induced edge embeddings.
    for letter in COPIES:
        for p, q in product(PARTS, repeat=2):
            assert edge_A(p, q) == edge_B(embed(letter, p), embed(letter, q))
    for letters in product(COPIES, repeat=2):
        for p, q in product(PARTS, repeat=2):
            x = tuple(embed(letters[k], p) for k in range(2))
            y = tuple(embed(letters[k], q) for k in range(2))
            assert edge_A(p, q) == edge_power(x, y)

    W0 = (None, 0)
    W1 = (0, None)
    W2 = (1, None)
    for W in (W0, W1, W2):
        for x, y in product(VERTICES, repeat=2):
            assert edge_B(x, y) == edge_power(line_map(W, x), line_map(W, y))
    assert {i for i, a in enumerate(W0) if a is None}.isdisjoint(
        {i for i, a in enumerate(W1) if a is None})
    assert {i for i, a in enumerate(W0) if a is None}.isdisjoint(
        {i for i, a in enumerate(W2) if a is None})

    first = line_image(W0) & line_image(W1)
    second = line_image(W0) & line_image(W2)
    assert first == word_image((0, 0))
    assert second == word_image((1, 0))
    union = first | second
    words = [word_image(pair) for pair in product(COPIES, repeat=2)]
    assert len(first) == len(second) == 2
    assert len(union) == 4
    assert all(len(w) == 2 for w in words)
    assert not any(union <= w for w in words)

    print("PASS: both distinct native lines are induced embeddings")
    print("W0 intersection W1: one A-word copy; size =", len(first))
    print("W0 intersection W2: another A-word copy; size =", len(second))
    print("Union of two overlaps:", len(union), "vertices")
    print("Any single A-word copy:", len(words[0]), "vertices")
    print("No single A-word copy contains the entire combined overlap")
    print("Scope: rank-history strategy counterexample, NOT Theorem 2.18")


if __name__ == "__main__":
    check()
