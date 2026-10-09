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

## 9 October: exact weak tests and U-irreducible localization

The new declarations form a strictly limited, proof-checked interface
for the 2019 transfer; they do **not** by themselves prove Lemma 2.28,
Lemma 2.31, or Theorem 2.18:

- PR #149: `IsUIrreducible`, `IsUHomomorphismEmbedding`,
  `IsUCompletion` and their basic embeddings. **Correction after
  checking the 2019 published Definition 2.15:** the original
  interface incorrectly required an induced test to be both U-closed
  and U-irreducible. Definition 2.15 only requires U-irreducibility.
  This branch removes the extra condition; the old #149 definition
  must not be cited as a complete verification.
- PR #150: `IsFreeAmalgam.weakInduce` restricts an arbitrary
  relational free-amalgam to a given vertex set and its exact
  inverse-image side/root sets. No closure assumptions or added
  vertices occur. The stronger
  `IsFreeAmalgam.weakInduce_withMaps` also records the pointwise
  formulas for the canonical side embeddings.
- PR #151: `IsUSubstructure.preimage_embedding`,
  `IsUClosed.induce_preimage_embedding`, and
  `IsFreeAmalgam.uIrreducible_side` show that a U-irreducible test
  **whose tested set is a U-substructure** of a free amalgam of
  U-closed sides lies in one of the sides. The theorem does not
  require the common gluing root to be U-closed.
- The exact U-homomorphism-embedding codomain factorization is
  `IsUHomomorphismEmbedding.weakImage` in
  `ClosureUHomWeakImage.lean`: the induced codomain is on precisely
  `Set.range f`, not the generated U-closure. This is only a
  **codomain** result; it does not assert that a U-homomorphism-
  embedding restricts to arbitrary weak *source* tests.

PRs #149--152 passed complete Lean builds and permitted-axiom audits,
  but build success alone did not certify fidelity to the published
  definitions. The present semantic correction is separately checked
  against Definition 2.15 and must pass a new full build and audit.

**TODO — next actual proof step.** In the 2019 partite Picture
construction, supply the U-homomorphism-embedding projection and the
U-closed witness invariant using the above exact-image and
U-irreducible-side lemmas. Check the nonclosed weak source tests
separately; the side localization hypothesis is not automatic for
them. For Lemma 2.31, provide K-valued local completions at the
original vertex bound and explicitly produce any simultaneous relative
extension certificates required by a mixed attachment. Neither
independent completions nor replacement by generated closure hulls
suffice.

### Definition 2.15 semantic correction (9 October)

The printed 2019 definition of a U-homomorphism-embedding requires a
homomorphism to restrict to an embedding on **any U-irreducible
substructure**. The former #149 predicate quantified only over
U-closed U-irreducible substructures, hence was too weak. In the
updated `IsUHomomorphismEmbedding`, `embeddingOn`, and
`ClosureUHomWeakImage`, U-irreducibility is the sole test hypothesis.
The previously checked U-irreducible localization lemma (#151)
remains valid only for U-substructures; it does not assert all weak
induced subsets localize.

These facts were compared with the publisher's Definition 2.15:
https://www.sciencedirect.com/science/article/pii/S0001870819304098

### Relative U-substructures in arbitrary weak tests (9 October)

The published Definition 2.22 distinguishes a **U-substructure of B**
(closure tuples of B rooted in it do not leave it) from a structure
that is intrinsically U-closed.  These conditions agree for
substructures of a U-closed ambient structure by Lemma 2.23(1), but
can differ for an arbitrary nonclosed weak induced test.

The two candidate notions of U-irreducibility therefore need an
explicit semantic comparison:

- `IsUIrreducible` (PR #149) prohibits free decompositions whose
  two sides are *intrinsically U-closed*.
- `IsURelativelyIrreducible` (PR #155) prohibits free decompositions
  into two proper *U-substructures of the tested structure*, in the
  relative sense of Definition 2.22.

The relative version has the useful weak-test theorem
`IsFreeAmalgam.uRelativeIrreducible_weak_side`. It applies to **every**
induced vertex set in a free amalgam of U-semi-closed structures
over a U-closed common root, with no assumption that the tested set
or its projected image is U-closed. It relies on the verified
relative side-range lemmas from PR #154 and the exact weak-amalgam
restriction from PR #150.

**Definitional fidelity:** The equivalence
`IsUClosed.uIrreducible_iff_relative` is now formalized for a
**U-closed ambient structure**.  It uses the new reverse closure
transport for exact embedded U-substructure ranges (PR #157) and
the previous range-closure lemma; mark it validated only once its
own full build and axiom audit have passed.

**TODO (nonclosed tests):** Determine whether the printed phrase
"proper U-closed substructures" in Definition 2.15 means intrinsically
U-closed structures or subsets closed relative to the ambient
structure. Do not silently identify the two **on a non-U-closed weak
test**, and do not use the new weak-test theorem to claim Lemma 2.28
or 2.31 complete.  The closed-ambient equivalence does not settle
this remaining interpretation question.

### The correct finite induction parameter: U-size (Definition 2.25)

The published Lemma 2.30 is a **j to j+1 induction on U-size**,
not an induction on the cardinality of arbitrary weak image tests.
U-size is the least cardinality of a vertex set whose U-closure is
the entire structure.  Its source-relative closure hull and rank are
now defined in `Ramsey/ClosureUSize2019.lean`:

- `UClosureHull`: intersection of all ambient-relative U-substructures
  containing the specified set;
- `UClosureHull_isUSubstructure`, `UClosureHull_minimal` and
  `UClosureHull_idempotent`: the closure operator's basic properties;
- `IsUClosed.induce_UClosureHull`: the induced hull is U-closed when
  the ambient structure is U-closed;
- `USize`, `USize_spec` and `USize_le_card`: the minimal generating
  rank for finite structures and its elementary cardinal bound.

This is deliberately NOT an instruction to close a projected test
p[S]. Weak projected images remain induced on precisely p[S].
Lemma 2.31 finishes by taking n passes on U-size and observing that
every U-substructure with at most n vertices has U-size at most n.
The U-size induction and the finite-vertex conclusion therefore need
separate transport lemmas.

**TODO:** Formalize the actual Lemma 2.30 step with U-size, preserving
the exact weak-image cardinalities needed during one Picture pass;
then derive Lemma 2.31 with n iterations. Neither is proven by the
closure-rank API alone. Only mark the above declarations validated
after a full Lean build and axiom audit on their PR head.

### Adversarial 2019 Lemma 2.29 weak-test audit

Definition 2.15, taken literally with decomposition into **intrinsically
U-closed** sides, has a surprising consequence: if a weak induced test
contains a valid closure root but omits every closure tuple over that
root, the test is automatically U-irreducible, even if it has many
other unrelated vertices. This is `IsUIrreducible.of_missing_closureTuple`
(PR #162), strengthened for **arbitrary induced weak tests** by
`IsUIrreducible.of_missing_tuple_in_weak_test`.

The cardinal obstruction
`not_allIntrinsicUIrreducibleTestsEmbed_of_large_missing_test`
says that if such a weak test has more vertices than B, then it is
impossible that *every* intrinsic U-irreducible induced substructure
embed into B. It does not require generated closure or additional
assumptions about the ambient root's missing outputs.

This directly challenges the **unqualified** invariant in the proof
of Lemma 2.29, which says that the initial disjoint union of B-copies
and later free amalgamations introduce no new U-irreducibles.
For example, in an ambient U-closed structure with a unary closure
root r and distinct output o, a weak test containing r but not o can
also contain vertices from multiple B-copies. Its intrinsic
U-irreducibility follows from the missing-output principle; its
localization to a single B-copy does NOT follow from the existing
intrinsic definition.

**TODO — priority semantic decision:** Check the proof against the
published Definition 2.15 and determine whether 'U-irreducible
substructure' must mean a U-closed substructure, or indecomposability
into *relative* U-substructures (Definition 2.22), for the asserted
copy-coverage invariant. The equivalent notions for U-closed
structures (PR #162) do not resolve nonclosed weak tests. Until this
is repaired, do not label Lemma 2.29, 2.28 or 2.30 as validated.

The new intrinsic obstruction theorem is deliberately conditional.
A concrete finite counterexample to the **full stated Lemma 2.29**
still requires instantiating A,B,C0 and their Ramsey assumptions.
Do not claim that theorem refuted solely from the conditional test.

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
   image's closure hull. U-semi-closedness and the basic U-homomorphism-
   embedding interface are now formalized. What remains here is their
   application to the full 2019 Ramsey-witness and completion induction,
   especially the not-necessarily-U-closed small tests. Definition 2.15
   must be represented WITHOUT an additional closedness hypothesis
   on U-irreducible source tests.
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
