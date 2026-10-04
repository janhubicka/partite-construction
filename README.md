# Partite construction

Reusable Lean formalization of structural Ramsey theory from Appendix A of
*Twenty years of Nešetřil's classification programme of Ramsey classes*.

## Checked endpoints

The **non-induced relational construction** is checked end to end: the finite
Partite and Picture Lemmas, initial pictures, finite iteration, increasing
placements, and order completion. `Partite.orderedRamsey` is the unconditional
ordered Nešetřil–Rödl conclusion.

The **relational induced construction** is also checked end to end.
`Partite.Induced.inducedConstruction` returns the witness with a finite trace
certifying the irreducible-image invariant at every stage.

The **positive-arity recursive construction with set-valued functions** is
assembled through domain-aware semi-closed pictures, singleton reduction,
and half-closed repair. `Structure.orderedClosedGraphRamsey` proves the survey's
`thm:models2`. Full functional embeddings are equivalent to closed graph
embeddings; arbitrary full homomorphisms are not identified with weak graph
homomorphisms.

The **strict relational sparsening theorem with A and B irreducible** is
proved through a complete binary-relation expansion and the checked iterated
construction. This bypasses, rather than proves, the stronger synchronized
`thm:tree_invariant` under mere irreducibility of A.

`Functional/FreeAmalgamClosed.lean` unifies both local closure observations,
including their converses and constants. `Partite.HalfClosed.ramseyPartiteWitness`
exposes the exact finite half-closed witness without requiring its input D to
be U-transversal.

The functional induced invariant / EHN class transfer and the strong
synchronized tree invariant have separate outstanding obligations. See the
[current coverage map](docs/appendix-a.md) and [roadmap](ROADMAP.md), not the
historical progress logs, for the exact boundary.

Hales–Jewett is imported from a pinned commit of
[lean-successors](https://github.com/janhubicka/lean-successors) and converted
to the finite fixed-length form.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Dedup
lake build PartiteConstruction PartiteConstruction.Functional.FreeAmalgamClosed PartiteConstruction.Functional.HalfClosedTheorem PartiteConstruction.Functional.QuotientFibreObstruction
lake env lean CheckAxioms.lean > axioms.log
lake env lean CheckClosureAxioms.lean >> axioms.log
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean CheckClosureAxioms.lean
```

The toolchain and dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`. CI caches both the compiler and Lake workspace. Every
audited declaration must use only the standard logical axioms; missing audit
results, `sorryAx`, and unproved custom axioms are rejected.

## Library layout

`Relational/` and `Structure/` contain the reusable structural definitions;
`Partite/` contains the relational constructions; `Functional/` contains
closure, graph encoding, semi-closed recursion, and functional interfaces;
`Iterated/` contains weak-substructure iteration, tree witnesses, sparsening,
and separately named obstruction/history diagnostics. `Ramsey/` and
`HalesJewett/` provide the finite combinatorial inputs and ordered endpoints.
