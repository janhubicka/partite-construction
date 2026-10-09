# How the verified constructions relate to *All those Ramsey classes* (2019)

> **8 October semantic audit:** The original 2019 paper treats function
> symbols as **partial** maps; its homomorphisms need not reflect undefined
> inputs. Our checked EHN weak projections are in fact original-style
> partial homomorphism-embeddings by `originalPartialHE_iff_EHN`.
> The 2026 full-total-fibre sparsening counterexample and the native-power
> no-full-fibre theorem must **not** be treated as counterexamples to the
> 2019 theorems. See `docs/original-partial-homomorphism-audit.md`.

## Exact target statements

Hubička--Nešetřil, *All those Ramsey classes (Ramsey classes with
closures and forbidden homomorphisms)*, Advances in Mathematics 356
(2019), article 106791, DOI 10.1016/j.aim.2019.106791.

- **Theorem 2.19 (Ramsey theorem for finite models)**: all finite
  linearly ordered relation/function structures form a Ramsey class.
  **Already implied**, now with the explicitly named Lean declaration
  `Structure.allThoseRamseyClasses_theorem_2_19`. The theorem is for
  arbitrary function arities, including nullary functions, with full
  embeddings. It instantiates the fully checked
  `Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity` to
  `allStructures`. No full global projection and no tree sparsening
  are assumed.
- **Theorem 2.18 (multiamalgamation theorem)**: every
  `(R,U)`-multiamalgamation class is Ramsey. **NOT YET deduced in this
  generality.** Such a class has strong amalgamation, rather than
  necessarily free amalgamation, and its locally finite completion
  axiom refers to *U-closed* structures and completions of arbitrary
  not-necessarily-U-closed small substructures.

## What the partite development supplies

1. The unrestricted ordered relational Ramsey theorem and the genuine
   functional all-arity EHN Ramsey theorem are already checked.
2. For *relational* languages the strict sparsening theorem
   `Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all`
   constructs a Ramsey witness with a global homomorphism-embedding
   back to the original Ramsey structure, strict B-tree completions
   for all small induced tests of a prescribed vertex size, and
   extension of all irreducible induced substructures into a B-copy.
3. In genuine function languages the native partite construction has
   a **weak EHN** projection, a complete full-function Ramsey arrow,
   and weak-to-weak projected image semantics. This does not itself
   supply strict *functional* B-tree completions (the native-power
   staircase obstruction verifies that generic strict-power
   preservation is false). Those stronger strict functional targets
   are not a premise of the published Theorem 2.18 after converting
   closures into the proper relational language.
4. The existing full-functional loose-tree Ramsey theorem is stronger
   in a different direction but its loose tree property must not be
   substituted for either the printed strict-relational sparsening or
   the U-closed local-completion requirement.

## New, checked-on-CI-after-merge transfer interface

`Ramsey/CompletionTransfer.lean` matches the final colouring transfer
in Definition 2.16 and the proof of Theorem 2.18.

`CopywiseCompletion B C D f` is a **single vertex map** `f:C->D`
whose restriction to every *B-copy* in C coincides with a genuine
embedding into D. It need not be a global homomorphism (in particular,
it need not reflect relations outside B-copies or be globally injective).

`CopywiseCompletion.of_irreducible_extension` shows that this map also
respects every A-copy when A is irreducible and the sparse C has the
verified irreducible-to-B-copy extension property.

`arrow_of_copywiseCompletion` transfers the structural Ramsey arrow
through this map; the transferred colouring depends only on the image
of each A-copy, and the B-copy restriction supplies the final embedding.

`ramsey_of_sparse_copywise_completion` combines these with strict
relational sparsening. Its extra premise says that every sparse witness
with the specified map, local tree property and B-copy coverage
receives a K-valued B-copywise completion. This is a **sufficient**
completion criterion, not a restatement of Definition 2.17 and not
proof of the full Theorem 2.18.

## Fully checked relational closure lemmas

The following are checked on an immutable Lean proof head
`70f7376667b8313d830a08cc262cc0005d530ef0` (GitHub Actions
`37881982179`, full build and permitted-axiom audit successful):

- `IsUClosed.induce_iff_USubstructure` — Lemma 2.23(1), without
  enlarging the induced vertex set;
- `Embedding.range_isUSubstructure` — images of full embeddings
  between U-closed structures are exact U-substructures;
- `IsFreeAmalgam.closureTuple_hasRoot_all` — no improper
  closure-relation tuple appears in a free amalgam;
- `IsFreeAmalgam.isUClosed` — Lemma 2.23(2), including existence
  and uniqueness of the closure tuple over every irreducible root.

The common overlap must **itself** be U-closed. If the overlap only
contains the inputs of a closure relation, the two sides may supply
different outputs, so the free amalgam need not be U-closed.
The result cannot be applied directly to an arbitrary weak projected
image.

## Gaps to obtain exactly Theorem 2.18

1. **Closure description (PARTLY COMPLETED)**: the general relational
   `ClosureRule`, `ClosureDescription`, `IsUClosed`, and vertex-exact
   `IsUSubstructure` are formalized in `ClosureDescription2019.lean`.
   Lemma 2.23(1) is proved: induced U-closedness is exactly the
   U-substructure condition on the existing set. Full embeddings have
   U-closed images (`ClosureEmbeddingRange.lean`). **Lemma 2.23(2) is
   also complete:** `IsFreeAmalgam.isUClosed` in
   `ClosureFreeAmalgamCompletion.lean` proves that a free amalgam of
   U-closed structures over a U-closed common root remains U-closed,
   including unique closure tuples. The proof does not take any weak
   image's closure hull. Still required here: the further U-semi-closed
   and U-homomorphism-embedding interfaces needed by the general
   2019 Ramsey witness and completion induction.
2. **Lemma 2.28 interface**: produce a U-closed Ramsey witness with
   U-homomorphism-embedding to C0. The native function proof should
   be reused *via* the closure relational encoding, but without
   replacing a weak image by its generated closure.
3. **Lemma 2.31/local step**: given K strong amalgamation and the
   relevant U-closed irreducible roots, show that the bounded
   induced tests of the constructed C admit (K,U)-completions, with
   the **same number of tested vertices** (not U-generated vertices).
   This is the key bridge from strict local tree pictures to the
   published local finiteness axiom.
4. **Class completion and colouring transfer**: invoke the exact
   locally finite completion axiom to get a K-completion of C
   relative to B-copies. The colouring-transfer part is already
   encoded by `arrow_of_copywiseCompletion_inClass`.

### Independence from the false 2026 sparsening assertion

The original arbitrary-function *full-projection + strict-functional-tree*
sparsening conclusion in the 2026 survey is refuted by a checked total
binary-operation counterexample. Neither Theorem 2.18 nor the current
formulation of Theorem 2.19 of the 2019 paper asserts that false
sparsening conclusion. The 2019 transfer deliberately permits a map
which is only a completion on the relevant B-copies; this is why the
new proof interface retains exactly that weaker condition.

## Implementation discipline

Do not label Theorem 2.18 as proved until the general closure and
locally finite completion hypotheses are represented and the end-to-end
proof passes the full build and permitted-axiom audit. Continue with
small, green PRs and add validation markers only for exactly proved
statements. The published circulation text remains frozen.
