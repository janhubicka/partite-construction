# Why the uniform original-core rooted Picture invariant cannot replace the published two-case induction

**15 October 2026 — mathematical adversarial audit (hand proof; NOT Lean-certified).**

This note explains why the earlier exploratory conditional finite-star
interface in [PR #311](https://github.com/janhubicka/partite-construction/pull/311)
was closed. The conditional Lean lemmas in #308–#310 are not refuted,
but their proposed **uniform** copied-old-side relative-completion premise
is false already for ordinary relational graphs.

## A four-vertex counterexample

Work with ordinary undirected loop-free graphs; adding compatible orders
does not affect the argument. Take

* `A = K₁` (a single vertex),
* `Base = B = K₂` (one edge), and
* `D = K₃` (a triangle, with three partition labels 0,1,2).

An admissible old `D`-partite stage may consist of the **three-edge path**

```text
        v0 ------- v1 ------- v2 ------- v3
part:    0          1          2          0
```

Every edge projects to a distinct edge of `D`, so the part projection
is a valid original-2019 EHN homomorphism-embedding; the stage itself is
already a strict `K₂`-tree. Pick the copy `α : A → D` at part 0. The
selected support of this old stage is the two-point *independent* set
`S = {v0,v3}`.

Its genuine Hales–Jewett power core is discrete and has full embeddings
of `S` with the two vertices sent to distinct core vertices `c0,c3`.
Attach one copy of the old stage along such an embedding. Its exact
four-vertex closed test is

```text
       c0 ------- w1 ------- w2 ------- c3
         \_____________________________/
            both endpoints lie in the
            original HJ power core
```

The fixed original-core map `q : core → A → K₂` maps **both**
`c0,c3` to the same vertex `b` of the edge `K₂`.

Suppose a relative strict original-2019 partial-function `K₂`-tree
completion existed for the four-point test, with root map prescribed
by `q`. Every strict `K₂`-tree has an underlying forest: free gluing
copies of one edge along the empty set, one vertex, or an edge
cannot create a cycle. The completion would send the three-edge
path to a length-three closed walk starting and ending at the image
of `b`. A forest is bipartite and has no odd closed walk. Contradiction.

The obstruction persists even if arbitrary extra `K₂`-pieces may be
attached to the target. It is not caused by missing function-image
closure (this example has no function symbols), nor by the later
survey's stronger, already invalid total-fibre projection.

## A maximal-projection obstruction to **fixed A-label roots**

The small-projection example above is not the only reason a globally
fixed A-to-Base root map is too strong. There is also a three-vertex
**maximal** test. Again take Base=B=K₂ and D=K₃, but now take A=K₂
embedded into D on labels 0 and 2. The old D-partite stage is the
disjoint union of:

* a path `v0--v1--v2` with projected labels `0,1,2`, and
* an edge `u0--u2` with projected labels `0,2`.

The stage is a forest, hence already a strict B-tree, and all three
edges project to full B-copies of D. The selected A-support on labels
0,2 contains `v0,v2,u0,u2`: the edge `u0--u2` makes the selected
A-placement genuinely active, while `v0,v2` remain nonadjacent.

Choose a full line embedding of this support into its genuine
Hales--Jewett power core. Let the images of `v0,v2` be distinct core
vertices `c0,c2`. Attaching the old stage produces the exact
closed test

```text
      c0 -------- w1 -------- c2
part:  0           1           2
       \_____________________/
       both endpoints lie in
       the original HJ core
```

This test has **three vertices and three distinct projected labels**;
it is maximal for `n=3`. Its actual common root consists of the two
nonadjacent core vertices and needs two generators.

Nevertheless the globally fixed selected A-to-Base map sends `c0`
and `c2` to the **opposite** endpoints of Base=K₂. No strict
K₂-tree extension can accommodate the two-edge path while retaining
those prescribed images: every target is a bipartite forest, and an
even path must have endpoints in the same bipartition class.

Importantly, the CORRECT conditional maximal-mixed relative-extension
schema is not contradicted. It allows the two sides to choose a
**shared root completion** `Start` and map `q` for this particular
test. For example, both nonadjacent root vertices can be mapped to
one Base vertex, allowing the two-edge path to fold onto one edge.
This map is not the fixed part-label embedding, and that flexibility
is precisely what the false anchored invariant suppressed.

Thus **even maximal projected cardinality** does not justify the
fixed original-core root labels. Generator maximality is a
necessary guard on the two-case induction, not a sufficient
root-compatibility theorem.

## Why the actual published induction avoids it

The projected test is `{0,1,2}`, of cardinality **3**, whereas the
source test has **4** vertices. The original published two-case proof
uses the **small projected image** case and the preceding rank.
It does **not** impose a root-preserving strict completion with both
original-core endpoints artificially mapped to the same Base vertex.

For genuine set-valued functions the correct induction counts a finite
set `G` of **generators** of the closed test:

* if `|p[G]| < n`, use the predecessor rank on the closed hull of
  `p[G]`; this hull may contain arbitrarily many vertices;
* if `|p[G]| = n` with `|G| ≤ n`, then `p` is injective **on G**,
  but need not be injective on the entire function-closed test,
  including its common separator.

The last point is why the hard multi-generated mixed-root case remains
open. The validated `EHNNativeOriginalPartialMaximalMixedReduction`
and `EHNMaximalMixedHardRootReduction` express the correct boundary;
the new `ProjectedGeneratorDichotomy` records its elementary
maximality and collision consequences.

## Scope and implementation decisions

The fixed-core results from #308–#310 remain sound as **conditional
geometric interfaces** and as an exact initial-core theorem, respectively.
They must not be advertised as a route to an unconditional strict
functional Picture theorem unless the extra assumptions are established
in a suitably restricted regime.

PR #311's full finite-star implication itself was not the point at
issue: its uniform incoming-copy premise is false in the above
four-vertex example. Rather than merge a logically correct but
unusable wrapper, the draft was closed.

**Open task:** construct compatible strict relative B-tree extensions
only for the genuinely maximal projected-generator-rank mixed tests
whose exact closed separator is not one-generated, with ambient
A-copy/projected-history control as required in the printed theorem.
Do not rerun the already verified recursive Ramsey construction.

**Verification status:** the graph counterexample above is an
elementary hand proof; no Lean axiom-audit or formal counterexample
theorem is claimed by this document.
