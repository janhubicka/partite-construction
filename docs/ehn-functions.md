# EHN with set-valued functions: proof architecture and survey interface

## Public conclusions

The functional development has two related, but different, endpoints:

- `Structure.FreeAmalgamationClass.orderedRamsey` in
  `Ramsey/FreeAmalgamationFunctions.lean`: add arbitrary linear orders to a
  hereditary free-amalgamation class in a relation/function language.
- `Structure.orderedRamsey_forbidden_expansions` in
  `Ramsey/ForbiddenFunctions.lean`: forbid particular **ordered** structures
  whose order reducts are irreducible. This is the precise forbidden-pattern
  formulation used by the survey's `thm:HN`.

Both use genuinely set-valued functions, of arbitrary positive input arity.
The colour type is any finite nonempty type. All embeddings in the Ramsey
arrows preserve complete function fibres, equivalently they are closed
embeddings of the relational graph encodings. No irreducibility hypothesis
on the colouring structure A or target B is imposed by the class theorem.

The fixed-target endpoint `orderedRamsey_of_mem_target` needs only B in the
class: either an ordered A-copy embeds into B, so heredity puts A in the
class, or B itself is a vacuous witness.

The compiler and complete axiom audit, including these endpoints, are the
validation gate. A manuscript marker must be pinned to an immutable commit
whose full build and audit passed; adding an endpoint to this note is not a
substitute for that check.

## The essential distinction between maps

A full homomorphism satisfies

    f[F_A(x)] = F_B(f(x)).

A weak homomorphism requires only the inclusion from left to right, together
with preservation of relation tuples. The existing `Structure.IsHomomorphism`
convention is unchanged. The new projection predicate
`IsWeakHomomorphismEmbedding` is weak globally but agrees with a full embedding
on every full embedded irreducible substructure.

A generated quotient may merge input tuples and gain outputs from another
source fibre. It is therefore not a full homomorphism in general. The earlier
`QuotientFibreObstruction` example remains valid. This does **not** prevent
irreducibility from passing to a weak image.

## One reusable closed-hull lemma

`Irreducible.of_generated_weakHomomorphism` proves that if a weak image of an
irreducible structure generates its target under the functions, that target
is irreducible. Suppose the target were a free amalgam of two proper closed
sides. Their inverse images are closed; they cover the source and every
source relation or function incidence lies in one of them. Neither inverse
image is the whole source: otherwise the generating image would lie in one
proper closed side. This would be a proper free decomposition of the source.

Consequently, `Irreducible.functionClosure_weakImage` applies to the **closed
hull** of a coordinate image, even when the raw coordinate range is not
closed. This is the object on which the previous-stage irreducibility
invariant can legitimately be used. These local facts do not need finiteness
or positive arity and also apply to constants.

## The same power and a shorter line-map proof

`Functional/WeakInduced.lean` reuses the existing coordinate power, words,
lines, and Hales--Jewett theorem. Only weak projection preservation is needed
for a line map to be a full embedding. For the reverse inclusion on function
fibres, a parameter coordinate gives a source output. Its line image and the
original power output have the same part, so **output transversality of the
power itself** makes them equal. There is no need to repeat a variable-versus-
constant coordinate argument for uniqueness.

This simplification is also applied to the existing full-projection
`Induced.lineMap_func` proof, preserving its old interface and universe
polymorphism.

`Functional/WeakInvariant.lean` then proves that the power retains a weak
homomorphism-embedding projection. For a full irreducible E inside the power,
take the closed hull of each coordinate image. Each hull is irreducible by
the preceding lemma and embeds fully into A by the old invariant. These
coordinate embeddings give injectivity and relation reflection on E. For
function exactness, an output in A lifts in every coordinate hull; the lifts
have one common part and therefore form a power output. Closedness of E in
the power lifts that output back to E.

## Exactly one induced refinement pass

`FunctionalPartite.EHN.inducedConstruction` starts with an arbitrary full
Ramsey witness D. It does not assume D belongs to the desired class K.
Initial pictures contain the B-copies prescribed by every full B-embedding
into D. At each full A-placement alpha:

1. Restrict the old picture to the inverse image of alpha[A]. This support
   is closed because alpha is a full embedding and the projection is weak.
2. Apply the functional Partite Lemma to that restriction. Every full
   irreducible of its power embeds into A, so the finite irreducible member
   test puts the power in K.
3. Attach the prescribed old-picture copies over closed supports. These are
   full free amalgams, preserving both membership in K and the weak
   irreducible projection invariant.

There is one finite colour-canonicalization pass over the A-placements, then
the usual backward Ramsey extraction. The implementation's finite list of
binary free attachments realizes the star-shaped attachment of a **single
Picture step**; it is not another Ramsey iteration.

The initial disjoint attachment uses positive function arity. Starting with
one B-copy, rather than an arbitrary empty structure, also preserves nullary
relation data. No extra class-membership assumption about an empty structure
is introduced.

## Why the exact survey corollary needs an order invariant

Forbidding an unordered reduct would also forbid every one of its orderings,
which is stronger than the survey assumes. Instead run the same refinement
inside the auxiliary class consisting of structures that avoid the specified
ordered forbidden patterns and whose partial order already compares every
distinct pair on each full irreducible reduct.

`OrderTotalOnIrreducibles` is hereditary and preserved by full free
amalgamation: any embedded irreducible reduct lies in one side. Every fully
ordered source and target has this property. The final partial order maps
into the ordered initial witness, so it has a linear extension.

Completing the order cannot create a new forbidden embedding. On its
irreducible reduct, all comparisons were already present, and any linear
extension preserves them. `Embedding.beforeOrderCompletion` makes this
argument explicit. This gives `orderedRamsey_forbidden_expansions` without
changing the forbidden family or silently assuming that it contains all
orderings of its reducts.

## What this does not claim

The functional EHN route is not a proof of a globally fibre-surjective
partite projection. The survey's direct induced theorem needs the weak-map
formulation when functions are present. Its relational form is unchanged.

The function-language **iterated sparsening** theorem and the stronger
synchronized ambient-A tree invariant remain separate obligations. The
class-preserving one-pass argument neither needs nor establishes them.

The global Ramsey theorems here have a positive-input-arity hypothesis.
The local closure and weak-image lemmas allow constants, but this does not
supply the missing unrestricted Ramsey/initial-construction treatment for
nullary functions.
