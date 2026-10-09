"""Finite regression: closed U-irreducible need not be irreducibly generated.

Directed E is the root relation, R is the ternary closure relation.
Each E(a,b) has exactly one R(a,b,c), and c is a distinct vertex.
The induced root is E(0,1) on two vertices with no R tuples.
This checks subset-based free decompositions (full induced sides).

Run: python3 scripts/check_2019_uirred_seed.py
No third-party libraries. Computational evidence, not a Lean theorem.
"""
from itertools import combinations

V = frozenset(range(5))
CLOSURE = ((0, 1, 2), (0, 2, 1), (1, 3, 0), (2, 4, 0), (3, 4, 0))
ROOTS = tuple((a, b) for a, b, _ in CLOSURE)
TUPLES = tuple(frozenset(t) for t in CLOSURE)


def subsets():
    for n in range(len(V) + 1):
        for s in combinations(sorted(V), n):
            yield frozenset(s)


def hull(seed):
    result = set(seed)
    while True:
        enlarged = result | {
            c for a, b, c in CLOSURE if a in result and b in result
        }
        if enlarged == result:
            return frozenset(result)
        result = enlarged


def is_closed(s):
    return hull(s) == s


def is_ordinary_irreducible(s):
    # Every E edge is contained in its associated three-vertex R tuple.
    return all(any({u, v} <= t for t in TUPLES)
               for u, v in combinations(sorted(s), 2))


def is_free_decomposition(left, right):
    return (left != V and right != V and left | right == V
            and is_closed(left) and is_closed(right)
            and all(t <= left or t <= right for t in TUPLES))


def check():
    assert len(ROOTS) == len(set(ROOTS))
    assert all(a != b and c not in {a, b} for a, b, c in CLOSURE)
    assert all(sum((a, b) == edge for a, b, _ in CLOSURE) == 1
               for edge in ROOTS)
    assert is_closed(V)

    all_subsets = list(subsets())
    closed = [s for s in all_subsets if is_closed(s)]
    free = [(s, t) for s in closed for t in closed
            if is_free_decomposition(s, t)]
    seeds = [s for s in all_subsets if is_ordinary_irreducible(s)]
    generating_seeds = [s for s in seeds if hull(s) == V]
    generators = [s for s in all_subsets if hull(s) == V]

    assert not free
    assert not generating_seeds
    assert min(map(len, generators)) == 3
    assert all({3, 4} <= s and (1 in s or 2 in s) for s in generators)
    assert all(not ({1, 4} <= t) and not ({2, 3} <= t) for t in TUPLES)

    print("PASS: five-vertex model has one output per directed E-root")
    print("Proper closed free decompositions:", len(free))
    print("Ordinarily irreducible generating sets:", len(generating_seeds))
    print("U-size:", min(map(len, generators)))
    print("Minimal generators:",
          sorted(map(sorted, (s for s in generators if len(s) == 3))))
    print("Scope: auxiliary-generator counterexample, not Theorem 2.18.")


if __name__ == "__main__":
    check()
