# Partite construction

Reusable Lean formalization of structural Ramsey theory, starting with the
non-induced partite construction in Appendix A of the survey *Twenty years of
Nešetřil's classification programme of Ramsey classes*.

The first milestone proves the finite non-induced **Partite Lemma**, with induced
embeddings, for any finite colour type. It also provides reusable relational
structures, embeddings, Ramsey arrows, partite systems, a checked interface to
unary predicates, prescribed projections, and backward induction through
pictures. The Picture Lemma and the final unrestricted Nešetřil–Rödl theorem
remain to be formalized.

Hales–Jewett is imported from a pinned commit of
[lean-successors](https://github.com/janhubicka/lean-successors), then converted
to the fixed-length statement needed for a finite witness.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Dedup
lake build
lake env lean CheckAxioms.lean > axioms.log
python3 scripts/check_axioms.py axioms.log
```

`lean-toolchain` and `lake-manifest.json` pin the compiler and all dependencies.
CI caches the Lean toolchain and Lake workspace and checks the main theorem
axioms against the standard logical axioms only.

## Library organization

* `Relational/Basic`: relational languages, structures, induced embeddings,
  composition, induced substructures, and finite embedding sets.
* `Ramsey/Basic`: structural arrows and monotonicity under target embeddings.
* `HalesJewett/Finite`: the fixed-length finite theorem, including empty types.
* `Partite/Basic`, `Predicates`, `Projection`: partite systems and their interfaces.
* `Partite/NonInduced`: the concrete power, line embeddings, substitution, and
  finite Partite Lemma.
* `Partite/Fusion`: backward induction from explicit local picture properties.

See [the coverage map](docs/appendix-a.md) and [the roadmap](ROADMAP.md) for the
exact correspondence with the survey and the remaining obligations.
