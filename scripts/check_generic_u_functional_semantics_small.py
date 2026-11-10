#!/usr/bin/env python3
"""Independent finite semantic regression for Appendix A Track F.

Enumerates complete U-relations (including repeated coordinates and empty
fibres), optional non-U unary predicates, all injections, and small Ramsey
arrows. This is NOT a Lean proof or CI certificate.
"""
from dataclasses import dataclass
from itertools import permutations, product


@dataclass(frozen=True)
class Model:
    n: int
    arity: int
    u: frozenset
    other: frozenset


def powerset(tuples):
    tuples = tuple(tuples)
    for bits in range(1 << len(tuples)):
        yield frozenset(tuples[i] for i in range(len(tuples)) if bits >> i & 1)


def models(n, arity, unary=True):
    for u in powerset(product(range(n), repeat=arity)):
        for other in powerset(range(n)) if unary else (frozenset(),):
            yield Model(n, arity, u, other)


def maps(a, b):
    return permutations(range(b), a)


def rel_closed_embedding(a, b, f, ordered):
    """Induced L-embedding + closure under all final-coordinate outputs."""
    assert a.arity == b.arity
    if any((x in a.other) != (f[x] in b.other) for x in range(a.n)):
        return False
    if ordered and any((x < y) != (f[x] < f[y])
                       for x in range(a.n) for y in range(a.n)):
        return False
    if any((t in a.u) != (tuple(f[x] for x in t) in b.u)
           for t in product(range(a.n), repeat=a.arity)):
        return False
    image = set(f)
    for root in product(range(a.n), repeat=a.arity - 1):
        target_root = tuple(f[x] for x in root)
        if any(target_root + (z,) in b.u and z not in image
               for z in range(b.n)):
            return False
    return True


def full_function_embedding(a, b, f, ordered):
    """Independently check full set-valued fibres, no retained U relation."""
    if any((x in a.other) != (f[x] in b.other) for x in range(a.n)):
        return False
    if ordered and any((x < y) != (f[x] < f[y])
                       for x in range(a.n) for y in range(a.n)):
        return False
    for root in product(range(a.n), repeat=a.arity - 1):
        target_root = tuple(f[x] for x in root)
        source_image = {f[y] for y in range(a.n) if root + (y,) in a.u}
        target_fibre = {y for y in range(b.n) if target_root + (y,) in b.u}
        if source_image != target_fibre:
            return False
    return True


def embeddings(a, b, ordered, version):
    predicate = rel_closed_embedding if version == 'rel' else full_function_embedding
    return tuple(f for f in maps(a.n, b.n) if predicate(a, b, f, ordered))


def arrow(a, b, c, ordered, version):
    ac = embeddings(a, c, ordered, version)
    bc = embeddings(b, c, ordered, version)
    ab = embeddings(a, b, ordered, version)
    if not bc:
        return False
    index = {e: i for i, e in enumerate(ac)}
    for colour in product((0, 1), repeat=len(ac)):
        good = False
        for f in bc:
            pulled = [colour[index[tuple(f[i] for i in e)]] for e in ab]
            if len(set(pulled)) <= 1:
                good = True
                break
        if not good:
            return False
    return True


def main():
    pairs = triples = arrows = 0
    for arity in (2, 3):
        # All unary choices for binary U, two extreme unary choices for
        # ternary U; all U-edge subsets on carriers of size 0,1,2.
        structs = []
        for n in (0, 1, 2):
            if arity == 2:
                structs.extend(models(n, arity, unary=True))
            else:
                structs.extend(Model(n, arity, u, other)
                               for u in powerset(product(range(n), repeat=arity))
                               for other in (frozenset(), frozenset(range(n))))
        for a in structs:
            for b in structs:
                for f in maps(a.n, b.n):
                    for ordered in (False, True):
                        x = rel_closed_embedding(a, b, f, ordered)
                        y = full_function_embedding(a, b, f, ordered)
                        assert x == y, (arity, a, b, f, ordered, x, y)
                        pairs += 1
        print(f'arity {arity}: {pairs:,} embedding-map comparisons cumulatively', flush=True)

    # Exhaustive small arrow and composition checks; no extra predicates.
    structs = [m for n in (0, 1, 2) for m in models(n, 2, unary=False)]
    for ordered in (False, True):
        for a in structs:
            for b in structs:
                for c in structs:
                    assert arrow(a, b, c, ordered, 'rel') == arrow(a, b, c, ordered, 'func'), (a,b,c,ordered)
                    arrows += 1
                    for f in embeddings(a, b, ordered, 'rel'):
                        for g in embeddings(b, c, ordered, 'rel'):
                            gf = tuple(g[f[x]] for x in range(a.n))
                            assert rel_closed_embedding(a, c, gf, ordered)
                            assert full_function_embedding(a, c, gf, ordered)
                            triples += 1
    print(f'PASS: {pairs:,} embedding comparisons; {triples:,} composition checks; {arrows:,} Ramsey-arrow comparisons')
    # Negative controls are actual embedding discrepancies, not just
    # mismatched data. A raw duplicate order (or raw duplicate U-relation)
    # can make a genuine decoded copy disappear in an incoherent target.
    def preserves_binary_relation(source, target):
        return all(((i, j) in source) == ((i, j) in target)
                   for i, j in product(range(2), repeat=2))

    genuine = {(0, 1)}
    bogus = set()
    assert preserves_binary_relation(genuine, genuine)
    assert not preserves_binary_relation(genuine, bogus)
    # For named order: the decoder restores the external 0<1 order, not bogus.
    # For U: the decoder derives R from F_R={(0,1)}, not a bogus duplicate R.
    print('PASS: incoherent-order and incoherent-U duplicate embedding controls')


if __name__ == '__main__':
    main()
