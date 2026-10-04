# Partite construction

Reusable Lean formalization of structural Ramsey theory from Appendix A of
*Twenty years of Nešetřil's classification programme of Ramsey classes*.

## Main endpoints

The relational non-induced and induced constructions are end-to-end proved.
`Partite.orderedRamsey` gives the unrestricted ordered relational theorem;
`Partite.Induced.inducedConstruction` returns a witness and a finite trace
of the irreducible-image invariant.

The positive-arity recursive construction with genuinely set-valued functions
is assembled through domain-aware semi-closed pictures, singleton reduction,
and half-closed repair. `Structure.orderedClosedGraphRamsey` gives the survey's
`thm:models2`.

The **functional EHN theorem** is exported as
`Structure.FreeAmalgamationClass.orderedRamsey` in
`Ramsey/FreeAmalgamationFunctions.lean`. It applies to hereditary classes
closed under full free amalgamation, with arbitrary positive-arity set-valued
functions and finite nonempty colour types. Neither A nor B needs to be
irreducible. Every embedding in the Ramsey arrow is full/closed. Its
fixed-target variant needs membership only of B.

`Structure.orderedRamsey_forbidden_expansions` in
`Ramsey/ForbiddenFunctions.lean` gives the exact survey forbidden-pattern
form: forbidden structures may specify particular orders, and their order
reducts are irreducible. An explicit comparability invariant ensures that
order completion does not create new forbidden embeddings. This is not the
stronger assumption of forbidding all orderings of each forbidden reduct.

Both functional endpoints use the unrestricted recursive theorem followed by
**one class-preserving induced pass**. Their reusable geometric input is
irreducibility of the closed hull of a weak image. See the
[functional EHN proof guide](docs/ehn-functions.md) for the implementation and
its correspondence with the survey.

Strict **relational** sparsening with B irreducible and arbitrary A is proved
by `Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all`.
It bypasses the stronger synchronized `thm:tree_invariant` under mere
irreducibility of A. Functional iterated sparsening, that stronger invariant,
and constants in the global Ramsey construction remain separate obligations.

`Functional/FreeAmalgamClosed.lean` unifies the local closure observations,
including their converses and constants. The exact half-closed witness is
`Partite.HalfClosed.ramseyPartiteWitness`, with no input-D transversality
assumption.

## Map conventions

`Structure.IsHomomorphism` retains equality of function-value images.
`Structure.IsEHNHomomorphismEmbedding` uses weak preservation globally and
full embeddings on full irreducibles. The older
`Structure.IsWeakHomomorphismEmbedding` is the graph-encoding notion used by
weak-substructure iteration; it is not an alias for the EHN predicate.

Hales–Jewett is imported from a pinned commit of
[lean-successors](https://github.com/janhubicka/lean-successors) and converted
to the finite fixed-length form.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run:

```sh
set -e
lake exe cache get Mathlib.Tactic Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Dedup
lake build
lake env lean CheckAxioms.lean > axioms.log
lake env lean CheckClosureAxioms.lean >> axioms.log
lake env lean CheckEHNFunctions.lean >> axioms.log
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean CheckClosureAxioms.lean CheckEHNFunctions.lean
```

The toolchain and dependencies are pinned. CI checks the umbrella import,
all audit imports, and theorem dependencies. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; missing audit output, `sorryAx`, and custom
unproved axioms fail. New functional EHN modules disable automatic implicit
declarations. Survey markers must reference a successfully checked immutable
commit, not merely the presence of a theorem name.

See the [coverage map](docs/appendix-a.md) and [roadmap](ROADMAP.md) for exact
scope. Historical progress logs are retained under `docs/archive/`.
