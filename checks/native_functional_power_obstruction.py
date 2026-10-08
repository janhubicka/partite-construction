#!/usr/bin/env python3
"""Finite regression for the candidate native functional-power obstruction.

The target forest induction is mathematical, not certified by this program.
This checks the small combinatorial witness, its complete function fibres,
and finite forest-target homomorphism obstructions.
No external dependencies.
"""
from itertools import product

# E has three binary function incidences, one unique output per input pair.
edges = {(0, 0): "z00", (1, 0): "z10", (1, 1): "z11"}
xs = ((0, 0), (0, 1), (1, 1))
ys = ((0, 0), (0, 1), (1, 1))

def function_output(x, y):
    """F in the genuine tagged coordinatewise power E^2."""
    values = []
    for a, b in zip(x, y):
        if (a, b) not in edges:
            return None
        values.append(edges[a, b])
    return tuple(values)

matrix = tuple(tuple(function_output(x, y) is not None for y in ys) for x in xs)
outputs = {
    function_output(x, y)
    for x in xs for y in ys
    if function_output(x, y) is not None
}

assert matrix == (
    (True, False, False),
    (True, True, False),
    (True, True, True),
)
assert len(xs) == len(ys) == 3
assert len(outputs) == 6
assert len(xs) + len(ys) + len(outputs) == 12
assert len(set(matrix)) == 3
assert len(set(tuple(matrix[i][j] for i in range(3)) for j in range(3))) == 3
# This is the displayed K_2,2, with both sides distinguished by third vertices.
assert all(matrix[i][j] for i in (1, 2) for j in (0, 1))

def is_forest(mat):
    """Acyclicity of a finite bipartite adjacency matrix."""
    nx, ny = len(mat), len(mat[0])
    graph = [[] for _ in range(nx + ny)]
    for i in range(nx):
        for j in range(ny):
            if mat[i][j]:
                graph[i].append(nx + j)
                graph[nx + j].append(i)
    seen = set()
    def visit(v, parent):
        seen.add(v)
        for w in graph[v]:
            if w == parent:
                continue
            if w in seen or not visit(w, v):
                return False
        return True
    return all(v in seen or visit(v, -1) for v in range(nx + ny))

assert not is_forest(matrix)

def respects_complete_domains(xmap, ymap, target):
    """Full fibre equality implies exact reflection of domain nonemptiness."""
    return all(
        matrix[i][j] == target[xmap[i]][ymap[j]]
        for i in range(3) for j in range(3)
    )

# Diagnostic only: enumerate all forests on <=3+3 input vertices and all
# label-preserving maps of the displayed input vertices into them. A general
# impossibility proof uses injectivity from distinct row/column profiles and
# the forest invariant of *every* full B-tree, at arbitrary cardinality.
forest_count = 0
map_count = 0
for bits in product((False, True), repeat=9):
    target = tuple(tuple(bits[3*i+j] for j in range(3)) for i in range(3))
    if not is_forest(target):
        continue
    forest_count += 1
    for xmap in product(range(3), repeat=3):
        for ymap in product(range(3), repeat=3):
            if respects_complete_domains(xmap, ymap, target):
                map_count += 1
assert map_count == 0

print(f"OK: closed test has 12 vertices and six distinct F-values")
print(f"OK: domain matrix {matrix} has a K2,2 and pairwise distinct rows/columns")
print(f"OK: no full domain-preserving map into any of {forest_count} labelled 3x3 forests")
print("NOTE: general full B-tree forest preservation is not verified by this script")
