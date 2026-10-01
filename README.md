# Partite construction

Reusable Lean formalization of structural Ramsey theory, starting with the
non-induced partite construction in Appendix A of the survey *Twenty years of
Nešetřil's classification programme of Ramsey classes*.

The finite non-induced **Partite Lemma**, **Picture Lemma**, **finite
iteration**, and final ordered theorem are proved with induced embeddings. The
library also constructs initial pictures, preserves constraints on projected
relations, proves finite Ramsey for increasing tuples, extracts the required
increasing placements, and completes the order without losing the Ramsey
arrow.

`orderedRamseyFromProjections` exposes the structural argument with an
explicit `ProjectionRamsey` input. The theorem `increasingProjectionRamsey`
discharges that input from finite Ramsey, and `orderedRamsey` is the
unconditional ordered Nešetřil–Rödl conclusion used by the survey.

The **relational induced partite construction** is now verified end to end as
well: irreducibility and homomorphism-embeddings, positive coordinatewise
powers, the induced Partite and Picture Lemmas, the disjoint-union initial
picture, formally based stages, preservation of the irreducible-image
invariant, and the final Ramsey extraction. `Induced.inducedConstruction`
returns the final witness together with a typed trace certifying every
intermediate stage.

This milestone is deliberately relational. The survey's general notion of
set-valued functions is not silently treated as coordinatewise: independent
coordinate choices can create extra function values. Function/closure handling
remains a separate recursive-construction milestone (the survey's
`U`-transversal machinery).

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
* `Relational/Homomorphism`: relational irreducibility, homomorphisms, and
  homomorphism-embeddings, including composition and reflection on irreducibles.
* `Relational/Attachment`, `Partite/Attachment`: free attachment along an induced
  substructure, reflection of relations, extension of prescribed copies, and
  localization of irreducible substructures.
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
* `Partite/Induced`, `InducedAttachment`, `InducedPicture`: coordinatewise
  powers, the induced Partite/Picture Lemmas, and the projection invariant.
* `Partite/InducedInitial`, `InducedInvariant`, `InducedBased`, `InducedStep`,
  `InducedConstruction`: initial pictures, based stages, irreducible-image
  preservation, the finite trace, and the end-to-end relational theorem.
* `Ramsey/Finite`: finite Ramsey for strictly increasing tuples.
* `Ramsey/FromProjections`, `Ordered`: the final reduction, increasing-placement
  interface, and unconditional ordered conclusion.

See [the coverage map](docs/appendix-a.md) and [the roadmap](ROADMAP.md) for the
exact correspondence with the survey and the remaining obligations.
