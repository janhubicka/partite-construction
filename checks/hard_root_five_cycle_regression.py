#!/usr/bin/env python3
"""Finite regression for the maximal-mixed hard-root sparsening obstruction.

The vertices and chosen full support embedding are those described in
docs/maximal-mixed-hard-root-schema-counterexample.md.

This script checks only finite graph combinatorics. The theorem that strict
K2-trees are bipartite, and the abstract original-partial root-gluing
implication, are verified separately in Lean. The script does NOT certify
the full Lean EHN Stage counterexample on its own.
"""
from collections import deque


OLD_PART = {
    "a0": 0, "b4": 4, "b2": 2, "a3": 3,
    "u0": 0, "u3": 3,
}
OLD_EDGES = [
    ("a0", "b4"), ("b4", "b2"), ("b2", "a3"),
    ("u0", "u3"),
]

CORE_PART = {
    "c0": 0, "d1": 1, "c3": 3,
    "w0": 0, "w3": 3,
}
CORE_EDGES = [
    ("c0", "d1"), ("d1", "c3"),
    ("w0", "w3"),
]

SELECTED_PARTS = {0, 3}
SUPPORT_MAP = {"a0": "c0", "a3": "c3", "u0": "w0", "u3": "w3"}
TEST = {"c0", "d1", "c3", "b2", "b4"}
ROOT = {"c0", "c3"}


def norm(edges):
    return {frozenset(edge) for edge in edges}


def induced_edges(edges, vertices):
    return {e for e in norm(edges) if e <= vertices}


def is_forest(vertices, edges):
    """For a finite simple graph, DFS detects all cycles."""
    adjacency = {v: set() for v in vertices}
    for edge in edges:
        a, b = tuple(edge)
        adjacency[a].add(b)
        adjacency[b].add(a)
    visited = set()
    for root in vertices:
        if root in visited:
            continue
        todo = [(root, None)]
        while todo:
            u, parent = todo.pop()
            if u in visited:
                return False
            visited.add(u)
            todo.extend((v, u) for v in adjacency[u] if v != parent)
    return True


def is_bipartite(vertices, edges):
    adjacency = {v: set() for v in vertices}
    for edge in edges:
        a, b = tuple(edge)
        adjacency[a].add(b)
        adjacency[b].add(a)
    color = {}
    for v in vertices:
        if v in color:
            continue
        color[v] = False
        todo = deque([v])
        while todo:
            u = todo.popleft()
            for w in adjacency[u]:
                if w not in color:
                    color[w] = not color[u]
                    todo.append(w)
                elif color[w] == color[u]:
                    return False
    return True


def check():
    eo, ec = norm(OLD_EDGES), norm(CORE_EDGES)
    assert is_forest(OLD_PART, eo)
    assert is_forest(CORE_PART, ec)

    # EHN partite projection of each side to the complete graph K5:
    # any graph edge maps to an edge with two distinct endpoints.
    assert all(OLD_PART[a] != OLD_PART[b] for a, b in OLD_EDGES)
    assert all(CORE_PART[a] != CORE_PART[b] for a, b in CORE_EDGES)
    assert set(OLD_PART.values()) | set(CORE_PART.values()) == set(range(5))

    support = {v for v, p in OLD_PART.items() if p in SELECTED_PARTS}
    assert support == set(SUPPORT_MAP)
    assert len(set(SUPPORT_MAP.values())) == len(SUPPORT_MAP)
    assert all(OLD_PART[v] == CORE_PART[SUPPORT_MAP[v]] for v in support)
    assert {frozenset((SUPPORT_MAP[a], SUPPORT_MAP[b]))
            for edge in induced_edges(eo, support)
            for a, b in [tuple(edge)]} == induced_edges(ec, set(SUPPORT_MAP.values()))
    assert induced_edges(eo, support) == {frozenset(("u0", "u3"))}

    # The complete free amalgam only identifies the 4 support vertices.
    full_vertices = set(CORE_PART) | (set(OLD_PART) - support)
    full_edges = ec | {
        frozenset((SUPPORT_MAP.get(a, a), SUPPORT_MAP.get(b, b)))
        for a, b in OLD_EDGES
    }
    assert len(full_vertices) == 7
    assert len(full_edges) == 6

    # Exact closed test (in a function-free language every subset is closed).
    expected_cycle = norm([
        ("c0", "d1"), ("d1", "c3"), ("c3", "b2"),
        ("b2", "b4"), ("b4", "c0"),
    ])
    assert induced_edges(full_edges, TEST) == expected_cycle
    assert len(TEST) == 5
    assert {CORE_PART.get(v, OLD_PART.get(v)) for v in TEST} == set(range(5))
    assert not is_bipartite(TEST, expected_cycle)
    assert not is_forest(TEST, expected_cycle)

    # Full test pullback onto old and core: exact two-vertex independent root.
    in_core = TEST & set(CORE_PART)
    in_old = (TEST & set(OLD_PART)) | ROOT
    assert in_core == {"c0", "d1", "c3"}
    assert in_old == {"c0", "b4", "b2", "c3"}
    assert in_core & in_old == ROOT
    assert induced_edges(full_edges, ROOT) == set()
    assert is_forest(in_core, induced_edges(full_edges, in_core))
    assert is_forest(in_old, induced_edges(full_edges, in_old))

    # Mixedness: each side contributes vertices outside the common root.
    assert in_core - ROOT and in_old - ROOT
    print("PASS: two forests and a full A-support embedding")
    print("PASS: closed maximal-rank five-vertex test with 5 distinct parts")
    print("PASS: mixed independent two-generator root")
    print("PASS: induced test C5 is not bipartite")


if __name__ == "__main__":
    check()
