"""Finite regression for the proposed two-small-support cut criterion.

This checks a finite obstruction to an intermediate proof strategy, not
Theorem 2.18. Run with Python 3; no third-party packages are required.
It is an exhaustive computational check, not a Lean proof.
"""
from itertools import combinations

VERTICES = frozenset(range(4))  # a=0, r=1, s=2, b=3
LEFT = frozenset({0, 1, 2})
RIGHT = frozenset({1, 2, 3})
BOUNDARY = LEFT & RIGHT
OUTPUTS = {0: 1, 3: 2}
EDGES = frozenset(pair for pair in combinations(range(4), 2) if pair != (0, 3))


def subsets(vertices: frozenset[int]):
    ordered = sorted(vertices)
    for size in range(len(ordered) + 1):
        for chosen in combinations(ordered, size):
            yield frozenset(chosen)


def hull(seed: frozenset[int], ambient: frozenset[int] = VERTICES) -> frozenset[int]:
    """Use only the unary-function tuples present in this induced source."""
    if not seed <= ambient:
        raise ValueError("The seed must lie in the ambient carrier")
    current = set(seed)
    while True:
        grown = current | {y for x, y in OUTPUTS.items() if x in current and y in ambient}
        if grown == current:
            return frozenset(current)
        current = grown


def rank(ambient: frozenset[int]) -> int:
    return min(len(seed) for seed in subsets(ambient) if hull(seed, ambient) == ambient)


def closed(carrier: frozenset[int]) -> bool:
    return all(x not in carrier or y in carrier for x, y in OUTPUTS.items())


def irreducible(carrier: frozenset[int]) -> bool:
    return all(pair in EDGES for pair in combinations(sorted(carrier), 2))


def free_cover(left: frozenset[int], right: frozenset[int]) -> bool:
    atoms = [frozenset(pair) for pair in EDGES]
    atoms += [frozenset(pair) for pair in OUTPUTS.items()]
    return left | right == VERTICES and all(t <= left or t <= right for t in atoms)


def check() -> None:
    assert closed(VERTICES) and closed(LEFT) and closed(RIGHT) and closed(BOUNDARY)
    assert free_cover(LEFT, RIGHT)
    assert irreducible(LEFT) and irreducible(RIGHT) and irreducible(BOUNDARY)
    assert hull(frozenset({0, 3})) == VERTICES
    assert rank(VERTICES) == rank(LEFT) == rank(RIGHT) == rank(BOUNDARY) == 2
    small = [s for s in subsets(VERTICES) if len(s) <= 1]
    assert not any(BOUNDARY <= hull(s) for s in small)
    rank_one_closed = [s for s in subsets(VERTICES) if closed(s) and rank(s) <= 1]
    assert all(irreducible(s) for s in rank_one_closed)
    assert not any(free_cover(s, t) for s in rank_one_closed for t in rank_one_closed)
    print("PASS: closed free amalgam; both sides and boundary are irreducible")
    print("Ranks: whole=2, left=2, right=2, boundary=2")
    print("Single-generator target supports tested:", len(small))
    print("Supports containing the boundary after closure: 0")
    print("Closed rank-at-most-one substructures:", len(rank_one_closed))
    print("Free covers by two closed rank-at-most-one structures: 0")
    print("Scope: finite strategy regression, not a Lean proof or a Ramsey counterexample")


if __name__ == "__main__":
    check()
