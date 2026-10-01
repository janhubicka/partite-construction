# Partite construction

Reusable Lean formalization of structural Ramsey theory, starting with the
non-induced partite construction in Appendix A of the survey *Twenty years of
Nešetřil's classification programme of Ramsey classes*.

The finite non-induced **Partite Lemma**, **Picture Lemma**, and **finite
iteration** are proved with induced embeddings. The library also constructs
initial pictures, preserves constraints on projected relations, extracts a
monochromatic copy from a Ramsey family of placements, and completes the order
without losing the Ramsey arrow.

`orderedRamseyFromProjections` assembles the structural argument into one
theorem. Its `ProjectionRamsey` hypothesis is explicit: the ordinary finite
subset Ramsey theorem and its increasing-placement interface remain to be
formalized before claiming the unconditional Nešetřil–Rödl theorem.

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
* `Relational/Attachment`, `Partite/Attachment`: free attachment along an induced
  substructure, reflection of relations, and extension of every prescribed copy.
* `Relational/Order`: ordered expansions and order completion preserving arrows.
* `Ramsey/Basic`: structural arrows and monotonicity under target embeddings.
* `HalesJewett/Finite`: the fixed-length finite theorem, including empty types.
* `Partite/Basic`, `Predicates`, `Projection`: partite systems and their interfaces.
* `Partite/NonInduced`: the concrete power, line embeddings, substitution, and
  finite Partite Lemma.
* `Partite/Fusion`: backward induction from explicit local picture properties.
* `Partite/Operations`, `Picture`: restriction, relabelling, and the Picture Lemma.
* `Partite/Initial`, `Construction`: initial pictures and finite iteration, with
  all local existence hypotheses discharged.
* `Partite/Invariants`: preservation of constraints on projected relation tuples.
* `Ramsey/FromProjections`, `Ordered`: the final reduction and ordered conclusion
  from the explicitly stated combinatorial Ramsey input.

See [the coverage map](docs/appendix-a.md) and [the roadmap](ROADMAP.md) for the
exact correspondence with the survey and the remaining obligations.
