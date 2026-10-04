# EHN with set-valued functions: proof architecture and survey interface

## Public conclusions

The fully general endpoints are:

- `Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity` in
  `Ramsey/FreeAmalgamationFunctionsAllArity.lean`;
- `Structure.orderedRamsey_forbidden_expansions_allArity` in
  `Ramsey/ForbiddenFunctionsAllArity.lean`, the exact survey `thm:HN`.

Both allow genuinely set-valued functions of **arbitrary input arity,
including nullary functions/constants**.  Colour types are finite nonempty
types, and all embeddings in Ramsey arrows preserve complete function fibres.
No irreducibility assumption on A or B is needed for the general class
theorem.

The older positive-arity endpoints remain useful implementation layers:
`Structure.FreeAmalgamationClass.orderedRamsey` and
`Structure.orderedRamsey_forbidden_expansions`.

## Weak projections versus full embeddings

A full homomorphism has equality
`f[F_A(x)] = F_B(f(x))`.  An EHN weak projection only preserves incidences
forward globally, but its restriction to every full irreducible is a full
embedding.  This is `Structure.IsEHNHomomorphismEmbedding`.

This is deliberately different from the graph-encoding
`Structure.IsWeakHomomorphismEmbedding` used in weak-substructure iteration.
Ramsey arrows themselves always use full embeddings.

## Closed hulls and the power invariant

`Irreducible.of_generated_weakHomomorphism` proves that the target generated
by a weak image of an irreducible source is irreducible.  Hence the closed
hull of every coordinate image in the Hales--Jewett power is irreducible even
when the raw coordinate range is not closed.

This supplies the coordinate embeddings required to prove that the power
retains the EHN projection invariant.  Function exactness then follows by
lifting an output coordinatewise and using output transversality.

The line-map proof is correspondingly short: one parameter coordinate supplies
a preimage; output transversality of the whole power gives uniqueness.

## Constants: two formalized mechanisms

### 1. Rooted unrestricted Ramsey reduction

`Structure/NullaryRoot.lean` defines the canonical root
`A.nullaryRoot = <empty>`.  Every closed substructure contains it and every
full embedding maps it onto the target root.

The modules
`RootedReduction`, `RootedFunctor`, `RootedSplit`,
`RootedCorrectness`, `RootedFreeAmalgam`, `RootedClass`,
`RootedEmbedding`, `RootedOrder`, and `RootedCanonical`
formalize the whole fixed-root translation:

- encode/decode on the moving complement;
- full embedding equivalence on rooted structures;
- transport of concrete free amalgams and free-amalgamation classes;
- rigidity of the finite ordered canonical root;
- reconstruction of the global order from cut predicates and the witness order.

This yields
`Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity`.

### 2. Root-shared EHN initial picture

The class-preserving induced pass does not need to translate the class to the
rooted language.  Its only positive-arity dependency was the initial disjoint
picture.  `FunctionalPartite.EHN.initial_allArity` instead takes one B-copy
as the core and attaches every other placement over B's canonical nullary
root.  Two full placements of B in D map that root onto the same target root,
so a full root transport identifies the overlap.

The rest of the Picture/Hales--Jewett construction is unchanged, giving
`FunctionalPartite.EHN.inducedConstruction_allArity`.

## Exact forbidden ordered patterns

For particular forbidden orderings, the auxiliary class keeps both
F-freeness and `OrderTotalOnIrreducibles`.  This class is hereditary and
closed under full free amalgamation.  Final order completion cannot create a
new forbidden copy because every comparison on an embedded irreducible reduct
was already present before completion.

Using the unrestricted all-arity witness followed by
`inducedConstruction_allArity` gives
`Structure.orderedRamsey_forbidden_expansions_allArity` directly in the
original language.  There is no remaining constants reduction outside Lean.

## What remains separate

This work does **not** prove a globally fibre-surjective partite projection.
The checked EHN projection is weak globally/full on irreducibles.

It also does not settle functional iterated sparsening or the stronger
synchronized ambient-A tree invariant.  Those are separate Appendix A
obligations.
