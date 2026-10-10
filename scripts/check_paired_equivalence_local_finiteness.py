#!/usr/bin/env python3
"""Finite block-level audit for the fixed-control paired-equivalence obstruction.

The universal argument is in docs/paired-equivalence-local-finiteness-correction.md.
This checks the clique and equivalence-closure combinatorics; it does NOT
formalize the full structural local-finiteness implication in Lean.
"""
from itertools import combinations

TYPES = ["A", "B", "T", "C", "D"]
ORDER = {t: i for i, t in enumerate(TYPES)}
POSITIVE = {frozenset(e) for e in [("A", "B"), ("B", "C"), ("A", "T")]}


def equiv(x, y):
    return x == y or frozenset((x, y)) in POSITIVE


def instance(m):
    assert m >= 5 and m % 2 == 1
    back = [f"b{i}" for i in range(m)]
    ty = {f"b{i}": ("C" if i == m - 1 else
                      ("A" if i % 2 == 0 else "B"))
          for i in range(m)}
    gadgets = []
    for i in range(m - 1):
        tag = f"t{i}"
        ty[tag] = "D"
        gadgets.append(tuple(sorted((back[i], back[i + 1], tag),
                                    key=lambda v: ORDER[ty[v]])))
    ty["t*"] = "T"
    gadgets.append(tuple(sorted((back[0], "t*", back[-1]),
                                key=lambda v: ORDER[ty[v]])))
    positive, negative, adjacent = set(), set(), set()
    for gadget in gadgets:
        a, b, c = (ty[x] for x in gadget)
        assert equiv(a, b) and not equiv(a, c) and not equiv(b, c)
        for x, y in combinations(gadget, 2):
            edge = frozenset((x, y))
            adjacent.add(edge)
            (positive if equiv(ty[x], ty[y]) else negative).add(edge)
    return back, ty, gadgets, positive, negative, adjacent


def conflicts(subset, positive, negative):
    parent = {x: x for x in subset}

    def root(x):
        while x != parent[x]:
            x = parent[x]
        return x

    for edge in positive:
        if edge <= subset:
            x, y = edge
            parent[root(x)] = root(y)
    return [e for e in negative if e <= subset and
            len({root(x) for x in e}) == 1]


def check(m, cutoff):
    back, types, gadgets, positive, negative, adjacent = instance(m)
    assert m > cutoff
    blocks = list(types)
    cliques = 0
    for k in range(len(blocks) + 1):
        for c in combinations(blocks, k):
            if all(frozenset(pair) in adjacent for pair in combinations(c, 2)):
                cliques += 1
                assert k <= 3
                assert k < 2 or any(set(c) <= set(g) for g in gadgets)
    tested = 0
    for k in range(cutoff + 1):
        for c in combinations(blocks, k):
            tested += 1
            assert not conflicts(set(c), positive, negative)
    assert frozenset((back[0], back[-1])) in conflicts(
        set(back), positive, negative
    )
    print(f"m={m}, blocks={len(blocks)}, gadgets={len(gadgets)}, "
          f"closed clique supports={cliques}, "
          f"local supports up to {cutoff}={tested}: PASS")


if __name__ == "__main__":
    for m, n in [(5, 1), (7, 3), (9, 5), (11, 7)]:
        check(m, n)
