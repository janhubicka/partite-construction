# A seven-cycle already inside a line-only functional Picture

**Audit date:** 16 October 2026

**Scope:** This is a counterexample to a NAIVE claim that a single
Hales–Jewett **line-indexed** Picture step preserves strict
`B`-tree completability of all exact weak tests at the same size
bound. It does **not** disprove the original functional Ramsey
theorem, the line-indexed `PictureProperty`, or the intended
(corrected) sparsening theorem; the latter requires a genuinely
stronger geometric construction or local-history invariant.

All operations in this example are purely relational graphs.
Thus function-output transversality holds vacuously. The example
shows that transversality alone does not supply the missing mixed
strict-tree extension.

## Original control, base and old Picture

Take an undirected loopless graph language; graphs are interpreted as
symmetric binary relations.

- `A = Base = K₂`, a single edge (closed and irreducible; `A`
  is also hereditarily irreducible).
- Control `D = K₃` on vertices/parts `0,1,2` is used only as an
  **EHN part control** for this regression. Contrary to an earlier
  version of this note, it is **not** a Ramsey arrow for arbitrary
  colourings of unordered `A=Base=K₂` embeddings: colour an oriented
  embedding by whether its two vertices increase in an external linear
  order on `D`; reversing either embedded edge changes the colour.
  The two `A`-embeddings into any fixed `Base` edge therefore cannot
  be monochromatic. This is a limitation of the example, not a defect
  in the verified PictureProperty or selected-line construction.
- Let the old functional-partite system have vertices
  `a0,b0` in part 0, `a1,b1` in part 1, and `c` in part 2,
  with precisely these graph edges:

```text
a1 — a0 — c — b1 — b0
```

So **Old is the forest P₅**, hence itself a strict `K₂`-tree.
The part map `Old→D` is EHN: every irreducible full subgraph of
Old is a vertex or an edge and maps as a full embedding into
`K₃`. Projected irreducible `Base`-coverage holds as well.

Fix the placement `alpha:A↪D` using parts 0 and 1.
The **entire selected support** is
`R={a0,a1,b0,b1}`. It consists of two disjoint edges

```text
a0 — a1       b0 — b1
```

and is function-closed (the language has no functions).
The genuine Hales–Jewett alphabet has two full letters
`e_a` and `e_b`, embedding the selected K₂ onto
the respective edges.

## The genuine coordinatewise power is a matching

For any `N≥2`, the true partite HJ power `E=R^N` consists
of tuples `(x₁,…,x_N)` whose coordinates have the same part.
Its graph relation holds **coordinatewise**.
Each vertex in part 0 has precisely one neighbour in part 1:
replace `a0` by `a1` and `b0` by `b1` in every coordinate.
Thus **E is a matching of `2^N` edges** (and in particular is a
strict `K₂`-forest), not a naive union of untagged tuples.

A Hales–Jewett line is a word in the symbols
`p` (parameter), `a` (constant full letter `e_a`),
`b` (constant full letter `e_b`), with at least one `p`.
Its full line embedding `R↪E` is exactly the one used in
`Induced.weak_lineEmbedding` and maps a vertex `x` to the
tuple obtained by substituting `x` at each parameter coordinate
and the corresponding selected A-letter vertex at constants.
All maps are genuine full graph embeddings.

The line-only Picture construction attaches a fresh entire
copy of Old along each such full line `R↪E`. Each old copy
contributes just one new exterior vertex `c_W`; it is adjacent
to `W(a0)` and `W(b1)`. Every attachment is a genuine FULL
free amalgam over the closed complete selected support.

## Three actual HJ lines form an induced 7-cycle

For `N=2`, choose just these three lines:

```text
W₀=(b,p),   W₁=(p,a),   W₂=(p,p).
```

Write `c₀,c₁,c₂` for their distinct freshly attached copies
of `c`. Then the induced subgraph on the following **seven exact
vertices** is `C₇`:

```text
c₀ — (b0,a0) — (b1,a1) — c₁
 |                            |
(b1,b1) — c₂ — (a0,a0) --------+
```

More unambiguously, the ordered cycle is

```text
c₀, (b0,a0), (b1,a1), c₁, (a0,a0), c₂, (b1,b1), c₀.
```

The single core edge used is
`(b0,a0) — (b1,a1)`. The six other cycle edges come
from the three copied Old paths
`a0 — c — b1`. There are **no chords**: those four
core vertices have no additional mutual edges, and each
fresh `c_W` is adjacent only to its prescribed two support
images.

For **every N≥2**, append the same constant letter `a` to
each of these three line words in coordinates 3 through N.
Append `a0` to the displayed part-0 power vertices and
`a1` to the displayed part-1 vertices. The identical induced
seven-cycle survives. Hence choosing a *longer* Hales–Jewett
word length does not remove this counterexample.

Because strict `K₂`-trees are forests and therefore
**bipartite**, an odd cycle cannot even have a graph
homomorphism to a strict `K₂`-tree. In particular this
exact seven-vertex weak test has no strict functional
`Base`-tree completion under the original partial
homomorphism-embedding convention. There are no function
inputs or outputs to complicate this conclusion.

The executable finite regression
`checks/native_hj_line_only_seven_cycle.py` constructs the
genuine coordinatewise core, the complete finite family of
line attachments, and verifies the induced seven-cycle for
`N=2,3,4,5`. The argument above covers every `N≥2`.

## Consequences for the formalization

1. **Keep the proved Ramsey improvement.**
   `EHN.pictureLemma_lines` and
   `EHN.inducedConstruction_allArity_lines`
   (PR #363, kernel verified and merged) are correct.
   The line-only family is sufficient for ordinary HJ
   canonicalization and the Ramsey arrow.
2. **Do not claim strict weak-tree `Q` preservation by merely
   instantiating `pictureLemma_lines_preservingSupport`.**
   The binary-attachment `hAttach` hypothesis is FALSE for
   `Q = n`-vertex strict `K₂`-tree completability when
   `n≥7`, even when Old and the HJ core are forests,
   `A=Base=K₂` is irreducible, the part map is EHN,
   and the copied supports are full and closed.
3. **Do not confuse this with a counterexample to the final
   sparsening theorem.** Its construction must do MORE than
   unrestricted free attachments along all lines: refine the
   geometry, prune or valuate attachments, or keep
   construction-history/root compatibility sufficient to
   avoid the displayed mixed cycle.
4. **Count exact WEAK subsets**. The seven-cycle itself is
   vertex-exact and closed in this function-free example.
   Enlarging to function closures would not fix it.
5. **Retain transversal set-valued output fibres** in every
   functional Stage. The obstruction is relational and survives
   the stronger invariant vacuously.

This audit complements, but is distinct from, the earlier C₅
obstruction to an arbitrary-stage hard-root extension schema:
it occurs among **three genuine HJ LINE attachments** and hence
rules out a simpler naive line-only strict-locality induction.
It leaves open the necessary history-sensitive or additional
sparsening construction.
