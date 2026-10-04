# Appendix A: current coverage and exact scope

This map replaces the chronological status accumulation. The previous detailed
inventory is preserved verbatim in
[the historical coverage log](archive/appendix-a-before-closure-audit.md).
Old entries in that log are not current proof obligations.

## Checked construction routes

| Survey component | Public Lean endpoint or module | Exact scope |
| --- | --- | --- |
| Non-induced construction and ordered relational Ramsey theorem | `Ramsey/Ordered.lean`, `Partite.orderedRamsey` | Finite relational structures; induced embeddings; all local pictures constructed |
| Induced construction | `Partite/InducedConstruction.lean`, `Partite.Induced.inducedConstruction` | Relational language; finite trace and irreducible-image invariant |
| Functions as graph relations | `Functional/Closed.lean`, `Structure.embeddingEquivClosedGraph`, `Structure.arrow_ofGraph_iff_closed` | Full functional embeddings correspond to closed graph embeddings; not an equivalence of arbitrary homomorphisms |
| Closed Partite Lemma | `Functional/ClosedPartite.lean`, `Partite.Closed.Induced.partiteLemma` | U-transversal partite input |
| Closed-alpha Picture Lemma | `Functional/ClosedPicture.lean`, `Partite.Closed.Picture.pictureLemma` | The projection alpha is closed; this is the valid moreover clause of `lem:indpicutreU` |
| Domain-aware semi-closed Picture Lemma | `Functional/SemiClosedPictureProperty.lean`, `Partite.SemiClosed.Picture.pictureLemma` | The intermediate little picture is semi-closed, not required to be U-transversal |
| Half-closed construction, `lem:rpartite` | `Functional/HalfClosedTheorem.lean`, `Partite.HalfClosed.ramseyPartiteWitness` | Positive function arity; arbitrary finite nonempty colour type; no U-transversality assumption on input D |
| Recursive construction, `thm:models2` | `Functional/OrderedRecursive.lean`, `Structure.orderedClosedGraphRamsey` | Positive function arity, equivalently distinguished graph-relation arity at least two |
| Closure of amalgam sides, `obs:disaster2` | `Functional/FreeAmalgamClosed.lean`, `RelStructure.IsFreeAmalgam.sides_closed_iff` | Both directions; arbitrary free-amalgam diagram; constants allowed |
| Closure of a common substructure, `obs:solution` | Same module, `RelStructure.IsFreeAmalgam.common_image_closed_iff` | Both directions; neither the whole overlap nor either side is assumed closed |
| Strict relational sparsening | `Iterated/SparseningStrictBaseIrreducible.lean` | A and B irreducible; complete binary-relation expansion, checked iteration, and final support; does not depend on the unresolved strong `thm:tree_invariant` |

All namespaces in the table lie under `StructuralRamsey`. For applications,
import the indicated endpoint module rather than reproducing construction
stages or changing their assumptions.

## The simplifications

The local closure calculus has one master statement:

`C.FunctionClosedSet S` iff the inverse images of S in both sides of a free
amalgam are closed. Each side is closed iff the overlap is closed in the
opposite side. This proves the two survey observations uniformly and separates
local closure (which permits constants) from the positive-arity initial
construction. It is not a transversality theorem.

The half-closed witness endpoint hides `Stage` and the initial `Nonempty`
bookkeeping. It preserves the exact difference between an ordinary B-copy in
D and a closed B-copy in the output. The native nested-flattening theorems have
an additional outer-transversality hypothesis for a different reason; that
hypothesis must not be imported into the standalone half-closed statement.

The final recursive route is the domain-aware semi-closed route. The old
arbitrary-alpha free-attachment argument is not a dependency of
`orderedClosedGraphRamsey`. Its counterexample refutes that argument, **not**
the existence of every conceivable witness for the stronger standalone claim.

## Remaining manuscript obligations

1. **Strong synchronized tree invariant.** Under mere irreducibility of A,
   localizing whole irreducible copies does not settle simultaneous control of
   all intersections of ambient A-copies with an arbitrary partial boundary.
   Hereditary irreducibility and several projected-history variants are
   checked, but are not substitutes for the literal `thm:tree_invariant`.
   The strict sparsening endpoint above avoids this stronger invariant.
2. **Full functional induced invariant / EHN class transfer.** The active EHN
   branch is independent work. Unrestricted functional Ramsey plus a
   graph-embedding equivalence does not by itself prove the free-amalgamation
   class membership conclusion. Check the functional irreducible-image
   invariant and the exact homomorphism convention before upgrading the
   survey's transfer paragraph.
3. **Constants in the initial construction.** Local closure observations allow
   nullary functions; the disjoint-copy recursive construction currently uses
   positive arity. Do not transfer the latter restriction to the former.
4. **Editorial disposition of arbitrary-alpha `lem:indpicutreU`.** Keep the
   stronger statement separate or replace it by the checked domain-aware
   statement. Do not silently retain the invalid displayed attachment proof.

## EHN quotient regression

`Functional/QuotientFibreObstruction.lean` gives a finite, exact generated-image
example. On two points, F(false)={false} and F(true)=empty. Collapse the points
to one; the incidence-generated target has F(*)={*}. The collapse is a
surjective graph homomorphism but not a full set-valued-function homomorphism.
It proves that an arbitrary noninjective generated-image quotient cannot be
used as a full homomorphism without a fibre-congruence condition. This is not a
counterexample to EHN; it identifies the correct weak-map interface needed
in the proof.

## Validation discipline

CI builds every new module and audits all declarations listed in
`CheckAxioms.lean` and `CheckClosureAxioms.lean`. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. Compilation errors,
`sorryAx`, missing audit results, and unexpected extra axioms are failures.
Pin the survey's `validation.tex` only to an immutable commit whose complete
build and axiom audit succeeded.
