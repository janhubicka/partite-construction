# Partite construction

Reusable Lean formalization of structural Ramsey theory from Appendix A of
*Twenty years of Nešetřil's classification programme of Ramsey classes*.

## Main endpoints

The relational non-induced and induced constructions are checked end to end.
`Partite.orderedRamsey` gives the unrestricted ordered relational theorem and
`Partite.Induced.inducedConstruction` gives the induced partite construction
with its irreducible-image trace.

The recursive Ramsey construction for genuinely set-valued functions is
checked in its positive-input-arity form as
`Structure.orderedClosedGraphRamsey`.  The constants issue is removed at the
EHN level by the canonical fixed-root construction described below.

The **functional EHN theorem for arbitrary function arities, including
constants**, is
`StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity`
in `Ramsey/FreeAmalgamationFunctionsAllArity.lean`.  It applies to hereditary
classes closed under full free amalgamation, with finite nonempty colour types;
neither A nor B is assumed irreducible and every embedding in the Ramsey arrow
is full/closed.

The exact survey theorem is
`Structure.orderedRamsey_forbidden_expansions_allArity` in
`Ramsey/ForbiddenFunctionsAllArity.lean`.  Forbidden structures may prescribe
particular orders, and only their order reducts need to be irreducible.  The
order-completion invariant prevents creation of new forbidden ordered copies.

There are two complementary constant-handling mechanisms, both formalized.
The rooted-language reduction removes the canonical root
`A.nullaryRoot = <empty>`, produces a moving language whose functions all
have positive arity, transports embeddings/free amalgams/classes, and
reconstructs the order.  Separately, the class-preserving EHN pass itself now
handles arbitrary arities directly: `FunctionalPartite.EHN.initial_allArity`
amalgamates the initial B-copies over their canonical nullary root, and
`FunctionalPartite.EHN.inducedConstruction_allArity` performs the usual one
induced refinement pass.

The **strict relational sparsening theorem** with B irreducible and arbitrary
A is
`Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all`.
It bypasses the stronger synchronized tree invariant rather than proving it.

The **direct positive-arity functional n-pass construction** (without U-closed
relational stages or repeated recursive Ramsey work) is
`Structure.inducedRamsey_nativeFunctionalIteration_originalPartial_all`.
The stronger **corrected functional sparsening with final B-copy coverage**
is `Structure.sparseningRamsey_nativeFunctional_graphStrict_withBCover` in
`Functional/NativeIteratedFinalBCover.lean`. It preserves the full Ramsey
arrow, the original 2019 partial-function (EHN) global projection, strict
**relational function-graph** B-tree completions on every n-vertex weak test,
and extension of every irreducible to a genuine full B-copy. It does **not**
assert strict full-functional local B-trees. The native closed common
separator has a one-copy strict original-partial completion, but compatible
relative extensions over the same reducible separator remain to be proved.

The published Appendix A Picture induction is now available on one genuine
functional witness, not as independent existence proofs:
`FunctionalPartite.EHN.initial_weakTree_and_projectedCover`,
`FunctionalPartite.EHN.pictureLemma_weakTree_and_projectedCover`, and
`FunctionalPartite.EHN.inducedConstruction_weakTree_and_projectedCover`.
These are covered by the CI/axiom-verified merged PR #273. The exported
`Structure.sparseningRamsey_nativeFunctional_graphStrict_withBCover_unrestricted`
removes the ambient free-amalgamation class parameter. All four preserve the
exact weak-substructure vertex budget and concern strict **function-graph**
B-tree targets, not unproved strict full-functional local B-trees.

## Map conventions

`Structure.IsHomomorphism` retains equality of complete function-value
images.  `Structure.IsEHNHomomorphismEmbedding` uses weak preservation
globally and full embeddings on full irreducibles.  The older
`Structure.IsWeakHomomorphismEmbedding` is the graph-encoding notion used by
weak-substructure iteration; it remains a distinct interface.

## Build and audit

```sh
set -e
lake exe cache get Mathlib.Tactic Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Dedup
lake build
lake env lean CheckAxioms.lean > axioms.log
lake env lean CheckClosureAxioms.lean >> axioms.log
lake env lean CheckEHNFunctions.lean >> axioms.log
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean CheckClosureAxioms.lean CheckEHNFunctions.lean
```

CI builds the umbrella and the audit imports.  Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted; missing audit output,
`sorryAx`, and custom unproved axioms fail.

See [docs/appendix-a.md](docs/appendix-a.md),
[docs/ehn-functions.md](docs/ehn-functions.md), and [ROADMAP.md](ROADMAP.md) for
the exact current proof boundary.
