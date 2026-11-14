#!/usr/bin/env python3
"""Exhaustive finite Track E regression (Python, NOT a Lean theorem).

A=K1, B=K2, C=C5 disjoint union K1, control C0=K6.
Even a Ramsey arrow, original same-map HE, external B-test coverage,
and a control-side B-extension of EACH irreducible source image do not
force internal B-copy extension inside C.
Not a claim about actual outputs of the coordinated partite construction.
"""
from itertools import combinations, permutations, product


def powerset(vertices):
    return [frozenset(t) for n in range(len(vertices) + 1)
            for t in combinations(vertices, n)]


def full_embeddings(src_vertices, src_edges, dst_vertices, dst_edges):
    """All full induced graph embeddings, represented by vertex maps."""
    source = tuple(sorted(src_vertices))
    if len(source) > len(dst_vertices):
        return
    for images in permutations(dst_vertices, len(source)):
        f = dict(zip(source, images))
        if all(((u, v) in src_edges) == ((f[u], f[v]) in dst_edges)
               for u in source for v in source):
            yield f


def is_irreducible(vertices, edges):
    """For a binary relation only: the Gaifman graph is complete."""
    return all(u == v or (u, v) in edges
               for u in vertices for v in vertices)


def symmetric_edges(pairs):
    return {(u, v) for a, b in pairs for u, v in [(a, b), (b, a)]}


A = (0,)
B = (0, 1)
C = tuple(range(6))
control = tuple(range(6))
A_edges = set()
B_edges = symmetric_edges([(0, 1)])
C_edges = symmetric_edges([(i, (i + 1) % 5) for i in range(5)])
control_edges = {(u, v) for u in control for v in control if u != v}

a_copies = list(full_embeddings(A, A_edges, C, C_edges))
b_copies = list(full_embeddings(B, B_edges, C, C_edges))
assert len(a_copies) == 6 and len(b_copies) == 10

# Ramsey arrow C -> (K2)^(K1)_2: quantify every vertex colouring.
for colours in product((0, 1), repeat=len(a_copies)):
    colour = {e[0]: c for e, c in zip(a_copies, colours)}
    assert any(colour[b[0]] == colour[b[1]] for b in b_copies)

# The *same* map f=id : C -> K6 is a positive homomorphism and
# a FULL embedding on every irreducible induced test of C.
f = {v: v for v in C}
assert all((f[u], f[v]) in control_edges for u, v in C_edges)
tests = [S for S in powerset(C) if is_irreducible(S, C_edges)]
assert len(tests) == 12
control_b_copies = list(full_embeddings(B, B_edges, control, control_edges))
assert len(control_b_copies) == 30
for S in tests:
    assert all(((u, v) in C_edges) == ((f[u], f[v]) in control_edges)
               for u in S for v in S)
    # External B coverage, including the empty test:
    assert any(True for _ in full_embeddings(S, C_edges, B, B_edges))
    # Stronger: f[S] is covered by a B-copy in the CONTROL C0:
    assert any({f[v] for v in S} <= set(g.values())
               for g in control_b_copies)

# But the isolated source vertex is in no INTERNAL B-copy.
assert frozenset({5}) in tests
assert not any(5 in g.values() for g in b_copies)
# The global HE is genuinely weaker than a full global embedding:
assert (0, 2) not in C_edges and (f[0], f[2]) in control_edges

print("PASS: 64 vertex 2-colourings, 10 B-copies, 12 irreducible tests")
print("PASS: global same-map HE C -> K6 and external B-test coverage")
print("PASS: each irreducible f[S] extends to a B-copy in control K6")
print("PASS: isolated source vertex 5 has NO internal B extension")
