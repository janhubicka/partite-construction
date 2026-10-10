#!/usr/bin/env python3
"""Three-vertex U-size strict-drop regression (2019 Definition 2.25).

This tests the relational closure data directly; every designated
closure tuple has an irreducible singleton root, the required output
is unique on each root, and the entire ambient structure is U-closed.

The *weak induced* {a,b} has intrinsic U-size 2. Its U-closure in the
ambient U-closed structure is {a,b,r}, which has U-size 1 because r
generates both a and b. Thus equality with U-size of the weak source
cannot be asserted; only the <= inequality is generally valid.

This is a finite executable regression, NOT a Lean-certified refutation
of a published claim. Exact definitions are described in the paired
markdown audit note.
"""
from itertools import combinations

ALL = frozenset({"a", "b", "r"})
WEAK = frozenset({"a", "b"})
UNARY_P = frozenset({"a", "b"})
UNARY_Q = frozenset({"r"})
# R has arity two and an irreducible one-vertex P-root.
# S has arity three and an irreducible one-vertex Q-root.
RULES = (
    (UNARY_P, frozenset({("a", "r"), ("b", "r")})),
    (UNARY_Q, frozenset({("r", "a", "b")})),
)


def induced_tuples(relation, ambient):
    return frozenset(t for t in relation if set(t) <= ambient)


def is_u_closed(ambient):
    for roots, relation in RULES:
        tuples = induced_tuples(relation, ambient)
        if any(t[0] not in roots for t in tuples):
            return False
        for root in roots & ambient:
            if sum(t[0] == root for t in tuples) != 1:
                return False
    return True


def hull(seed, ambient):
    assert set(seed) <= ambient
    active = set(seed)
    while True:
        updated = set(active)
        for _, relation in RULES:
            for tup in induced_tuples(relation, ambient):
                if tup[0] in active:
                    updated.update(tup)
        if updated == active:
            return frozenset(active)
        active = updated


def u_size(ambient):
    vertices = sorted(ambient)
    return min(k for k in range(len(vertices) + 1)
               if any(hull(seed, ambient) == ambient
                      for seed in combinations(vertices, k)))


def main():
    assert is_u_closed(ALL)
    assert not is_u_closed(WEAK)
    assert hull(WEAK, ALL) == ALL
    assert hull({"r"}, ALL) == ALL
    assert hull({"a"}, WEAK) == frozenset({"a"})
    assert hull({"b"}, WEAK) == frozenset({"b"})
    assert u_size(WEAK) == 2
    assert u_size(hull(WEAK, ALL)) == 1
    print("PASS: ambient is U-closed with irreducible singleton roots")
    print("Weak B0={a,b}: U-size 2")
    print("Ambient hull cl(B0)={a,b,r}: U-size 1")
    print("The printed equality fails: 2 != 1; the <= inequality holds")


if __name__ == "__main__":
    main()
