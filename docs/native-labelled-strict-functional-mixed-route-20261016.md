# Marked-`A` labelled strict functional trees: a second route through the mixed Picture

**Status (16 October 2026):** The target-amalgamation and exact weak-map
gluing parts are proved in Lean, subject to the current PR's green CI and
axiom check. **Existence of the marked labelled side completions for the
actual Hales–Jewett Picture is not proved.**

## Scope: the native functional iteration

The recursive Ramsey theorem already supplies the closed genuine
function-language control. The subsequent induced/iterated EHN
construction stays in genuine functions and uses a
`FunctionalPartite.System` at every stage. In particular,

```
y,z ∈ F_P(x) and part(y) = part(z)  ==>  y = z.
```

The output-fibre transversality invariant is a field of `System`,
not an accidental consequence of reducing to singleton functions.
Coordinatewise HJ powers and actual functional attachments preserve it.

A bounded local test is **exactly** `C.weakInduce S`, and its projected
image is `D.weakInduce (part '' S)`. Do not replace either vertex set by
a function-closure hull. An EHN map is source-defined partial
homomorphism; undefined inputs are not reflected.

## An alternative to root-hit isolation: label the entire target

A *labelled strict B-tree over D* consists of:

1. A genuine strict full-functional `TreeAmalgam B _ T`.
2. An EHN projection `pT:T→D`.

The EHN condition automatically makes each nonempty function fibre map
bijectively, so every fibre is part-transversal. The new
`IsFreeAmalgam.labelledStrictTree_glue` combines two such targets
over a **full** common root, when their projections agree there.

For the maximal mixed source test, the target need not glue over the
possibly reducible weak **source** root. Instead, it can glue over two
*marked full copies* `eL:A↪TL` and `eR:A↪TR`, provided:

- The marked copies are contained in genuine irreducible B
  constituents of the strict target trees.
- Both control labels equal the **same full embedding** `alpha:A↪D`
  on *every* vertex of the marked A-copy, including those not hit by
  the source weak test.
- Each exact weak source side has an ambient-relative weak HE into
  its tree whose target label matches the source part projection.
- The actual weak common-root points map into those marked A-copies
  using the same root coordinate `q:RootSet→A`.
- Each side protects intersections with genuine ambient A-copies.

Then the target free amalgam identifies the two marked A-copies.
The weak source side maps agree on their common root and glue, the
target control map is EHN, and the whole witness automatically
preserves *every* projected-history predicate:

```
pTarget(f(x)) = partWhole(x)
f(x) = f(y)   ==>   partWhole(x) = partWhole(y).
```

This requires **neither** a separately chosen root label
`pG:Start→D` **nor** a root-hit-isolation condition. The price is
a stronger marked-and-labelled side-witness hypothesis.

Lean interfaces:

- `Functional/LabelledStrictFunctionalTreeGlue.lean`:
  `IsFreeAmalgam.labelledStrictTree_glue`.
- `Functional/LabelledWeakTreeHistoryGlue.lean`:
  `IsFreeAmalgam.labelledStrictTreeWeakHistory_glue_markedA`.
- `Functional/AmbientRelativeWeakTreeHistoryGlue.lean`:
  alternative common-root extension constructor, already merged.
- `Functional/NativePowerTransversalTree.lean`:
  genuine transversal Hales–Jewett power with one-copy strict target.

## The remaining real problem

Prove that, for the actual Hales–Jewett Picture's maximal projected-rank
mixed tests, the predecessor induction supplies two **marked and
D-labelled strict functional B-tree side completions** satisfying the
strong full-A label and weak-root alignment above.

The ordinary weak-history invariant
`SetAmbientRelativeWeakTreeWitness` by itself does not provide that:
it protects the *tested intersection* with each ambient A-copy, but
does not prescribe control labels for the rest of the target A-copy.
Identifying two marked target A-copies without agreement of their
labels on the entire A can destroy the global target EHN projection.

A genuinely stronger induction invariant may need to remember selected
A-copy labels even for vertices outside the tested intersection, or
allow extending predecessor witnesses by fresh labelled B-copies over
suitable rooted substructures. Do not assume such an extension is
automatic in a free-amalgamation class.

### Adversarial test: the ordinary-graph odd cycle

For `A=B=K₂`, an old two-edge path on labels 0–1–2 and a new
core edge on labels 0–2 form the classic mixed odd-cycle obstruction
to the **unrestricted** hard-root schema. The old path has a strict
edge-tree completion considered alone, but it cannot have a strict
edge-tree completion in which its two endpoints are also required
to lie at the endpoints of one marked full K₂-edge: this would
force an odd cycle in a bipartite forest target.

Hence the marked-A side-completion hypothesis is substantive. The
new theorem does **not** manufacture it and does **not** refute the
published functional sparsening theorem. It isolates the extra
construction-history information which the genuine HJ step must
supply if this stronger labelled route is to work.

## Acceptance criteria for further proof

- Retain irreducible **and closed** B in the intended survey theorem.
- Do not replay the recursive semi-closed/U-closed construction during
  the iterated functional stage.
- Retain transversal set-valued function images in every partite
  stage and labelled strict target.
- Count **exact** weak vertices; projection may collapse tested
  vertices but test size is never increased by functional closure.
- Mark genuine theorem statements as verified only after full Lean
  compilation and named axiom checks.
- Finish the ACTUAL maximal mixed Picture preservation. No
  unconditional global strict functional n-pass theorem is claimed
  merely from the conditional target-amalgamation lemmas.
