#!/usr/bin/env python3
"""Finite regression: genuine Hales–Jewett LINE-only Picture creates C7.

The source objects are an old P5 forest, its full selected two-edge
support, a genuine tagged coordinatewise partite power, and complete
full line attachments. For all N>=2 there is an induced 7-cycle,
so naïve n=7 strict K2-tree locality is not preserved even if
both the old Picture and the HJ core are forests.

The checker validates finite graph combinatorics. It is NOT a Lean
proof of the full EHN Stage construction and does NOT disprove the
corrected functional sparsening theorem.
"""
from collections import deque
from itertools import product

PART = {"a0": 0, "b0": 0, "a1": 1, "b1": 1, "c": 2}
R = ("a0", "b0", "a1", "b1")
R_EDGES = {frozenset(("a0", "a1")), frozenset(("b0", "b1"))}
OLD_EDGES = R_EDGES | {
    frozenset(("a0", "c")), frozenset(("c", "b1"))
}
LETTER = {
    "a": {0: "a0", 1: "a1"},
    "b": {0: "b0", 1: "b1"},
}


def edge(a, b):
    assert a != b
    return frozenset((a, b))


def adjacency(vertices, edges):
    graph = {v: set() for v in vertices}
    for e in edges:
        a, b = tuple(e)
        assert a in graph and b in graph
        graph[a].add(b)
        graph[b].add(a)
    return graph


def is_forest(vertices, edges):
    graph = adjacency(vertices, edges)
    seen = set()

    def walk(x, parent):
        if x in seen:
            return False
        seen.add(x)
        return all(walk(y, x) for y in graph[x] if y != parent)

    return all(x in seen or walk(x, None) for x in vertices)


def is_bipartite(vertices, edges):
    graph = adjacency(vertices, edges)
    color = {}
    for x in vertices:
        if x in color:
            continue
        color[x] = 0
        queue = deque((x,))
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    queue.append(v)
                elif color[v] == color[u]:
                    return False
    return True


def line_apply(symbols, vertex):
    """Actual FULL HJ line embedding of the selected support R."""
    return ("core", tuple(
        vertex if sym == "p" else LETTER[sym][PART[vertex]]
        for sym in symbols
    ))


def picture(n):
    """All LINE attachments to the real tagged coordinatewise power."""
    assert n >= 2
    core = {
        ("core", tuple(word))
        for p in (0, 1)
        for word in product(
            [x for x in R if PART[x] == p], repeat=n
        )
    }
    core_edges = {
        edge(x, y) for x, y in product(core, repeat=2)
        if PART[x[1][0]] == 0 and PART[y[1][0]] == 1
        and all(edge(x[1][i], y[1][i]) in R_EDGES
                for i in range(n))
    }
    assert len(core_edges) == 2 ** n
    assert is_forest(core, core_edges)

    # Every full line embedding; constants are FULL copies of A=K2.
    lines = [
        word for word in product(("p", "a", "b"), repeat=n)
        if "p" in word
    ]
    vertices = set(core)
    edges = set(core_edges)
    for word in lines:
        outside = ("outside", word)  # Fresh copy of Old's c vertex.
        vertices.add(outside)
        edges.add(edge(outside, line_apply(word, "a0")))
        edges.add(edge(outside, line_apply(word, "b1")))

        images = {x: line_apply(word, x) for x in R}
        assert len(set(images.values())) == 4
        # The FULL line map reflects BOTH edges and missing edges.
        selected = {
            edge(images[u], images[v])
            for e in R_EDGES for u, v in [tuple(e)]
        }
        induced = {
            edge(images[u], images[v])
            for u, v in product(R, repeat=2) if u != v
            if edge(images[u], images[v]) in core_edges
        }
        assert selected == induced
    return vertices, edges, core, core_edges, lines


def check(n):
    assert is_forest(set(PART), OLD_EDGES)
    assert len(R_EDGES) == 2 and len(OLD_EDGES) == 4
    vertices, edges, core, core_edges, lines = picture(n)

    # Three genuinely distinct FULL HJ lines, padded with constants
    # so the same C7 survives for every n>=2.
    tail = ("a",) * (n - 2)
    w0 = ("b", "p") + tail
    w1 = ("p", "a") + tail
    w2 = ("p", "p") + tail
    cycle = [
        ("outside", w0),
        line_apply(w0, "a0"),
        line_apply(w1, "b1"),
        ("outside", w1),
        line_apply(w1, "a0"),
        ("outside", w2),
        line_apply(w2, "b1"),
    ]
    assert len(set(cycle)) == 7 and set(cycle) <= vertices
    expected = {edge(cycle[i], cycle[(i + 1) % 7])
                for i in range(7)}
    induced = {e for e in edges if e <= set(cycle)}
    assert induced == expected, (induced - expected, expected - induced)
    assert not is_bipartite(set(cycle), induced)

    # Original part projection is EHN on the old P5 and preserves all
    # graph edges on the line-indexed picture. No functions exist,
    # so the per-function output-transversality axiom is vacuous.
    assert all(
        (PART[x[1][0]] if x[0] == "core" else 2) !=
        (PART[y[1][0]] if y[0] == "core" else 2)
        for e in edges for x, y in [tuple(e)]
    )
    print(
        f"PASS N={n}: Old=P5 forest; core={len(core_edges)} matching edges; "
        f"{len(lines)} HJ lines; induced C7 from three full line copies"
    )


if __name__ == "__main__":
    for n in (2, 3, 4, 5):
        check(n)
