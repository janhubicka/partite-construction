# Correcting the function-domain convention: 2019 versus 2026

**Verified 8 October 2026**, Lean PR #126.

## The original definition in *All those Ramsey classes* (2019)

In Hubička--Nešetřil, *All those Ramsey classes*, Advances in
Mathematics 356 (2019), §1.1, a function symbol is represented by a
GENUINELY PARTIAL operation

    F_A : Dom(F_A) ⊆ A^arity(F) → A.

A homomorphism f:A→B requires f(Dom(F_A)) ⊆ Dom(F_B) and
f(F_A(x)) = F_B(f(x)) **only for x ∈ Dom(F_A)**.
There is no implication from f(x) ∈ Dom(F_B) back to x ∈ Dom(F_A).
An embedding is a monomorphism that also REFLECTS function-domain
membership, as well as reflecting ordinary relation tuples.

This directionality is also essential in Proposition 2.20, which adds
explicit domain relations and closure relations to encode the
partial-function model as a U-closed relational model. The category of
homomorphism-embeddings is preserved by this relational encoding.

Authoritative published source:
https://www.sciencedirect.com/science/article/pii/S0001870819304098

## Different definition in the 2026 survey

Hubička--Konečný, *Twenty years of Nešetřil's classification programme
of Ramsey classes*, Computer Science Review 59 (2026), 100814, §2.1,
instead writes total set-valued operations

    F_A : A^arity(F) → P(A)

and requires **equality on all source tuples**:

    f[F_A(x)] = F_B(f(x)).

When undefined inputs are encoded by F_A(x)=∅, this also forces the
converse implication:

    F_B(f(x)) nonempty  ->  F_A(x) nonempty.

The 2019 definition does NOT impose this reflection on homomorphisms.
The survey itself says that singleton/empty fibres correspond to
partial functions, but this correspondence of objects does not
preserve the homomorphism notion as currently written.

Authoritative postprint:
https://arxiv.org/html/2501.17293v5

## Faithful Lean comparison

The existing `Structure` representation makes `func F x : Set A`
available at every input. We now define `InOriginalPartialDomain A F x`
as `(A.func F x).Nonempty`. This correctly models the 2019 operations
with one output where defined; it also permits nonempty multivalued
fibres but **does not** represent a *defined empty set-valued output*
separately from an undefined input. Such a richer convention would
need an additional domain predicate or `Option (Set A)`.

`Structure.IsOriginalPartialHomomorphism` requires preservation
of relations and **exact equality** of output fibres on every
defined source input only. The new fully checked theorem

    Structure.originalPartialHE_iff_EHN

proves this original partial homomorphism-embedding condition is
**equivalent to the existing EHN weak homomorphism-embedding**
for the nonempty-fibre encoding. The nontrivial direction follows
from the already axiom-checked

    IsEHNHomomorphismEmbedding.map_func_of_nonempty

which supplies full fibre equality whenever the source fibre is
nonempty, because the input-generated function-closed hull is
irreducible. The converse is just positive incidence preservation
plus the same on-irreducibles condition.

`Structure.Embedding.originalPartialDomain_iff` checks the
2019 requirement that genuine embeddings *do* reflect domains.

## Consequences of this semantic correction

1. **2019 Theorems 2.18/2.19 have NOT been refuted.** The original
   partial homomorphism-embeddings agree with the EHN maps actually
   carried by our native function construction.
2. **The literal total-fibre 2026 sparsening statement remains
   refuted**, under the survey's written definitions, by the
   separately checked total-binary-operation existential
   counterexample `PublishedTotalBinaryObstruction`. That proof
   deduces that EVERY source binary fibre must be nonempty;
   the deduction fails under the 2019 partial homomorphism.
3. **The genuine tagged native-power staircase DOES admit a
   strict one-copy B-tree completion** under original 2019 partial
   homomorphism-embedding semantics. This is checked at both the
   full power and its proper *function-closed 12-vertex test*:
       actualPower_originalPartialTreeCompletion
       staircase_originalPartialTreeCompletion
   The previously proved negative
       staircaseSupport_no_strictTreeCompletion
   is still valid for the DIFFERENT, stronger requirement of a
   total-fibre `Structure.IsHomomorphismEmbedding`. The combined
       staircase_originalPartial_yes_totalFibre_no
   verifies both conclusions about the **same closed test** in Lean.
4. This removes the **generic power-domain-cycle obstruction** to
   original-style strict local completions. It does not itself
   prove the whole (A,B,n)-locally-tree-like induction: the target
   of a stage's EHN map can be C0, which need not embed into B, and
   reducible-root compatibility can still require work.
5. The **weak-to-weak projected image convention stays necessary**:
   for vertex test S, use the weak induced structure on p[S], not
   its generated closure. A partial homomorphism may map an
   undefined source tuple to a defined target tuple; the image
   must not be assumed function-closed.

## Proposed next mathematical tasks

1. Refactor the optional strict-functional local-tree invariant to
   use the *original partial* homomorphism-embedding for completion
   maps and the original genuine *full* embeddings for B-tree gluing.
   Do not change the already verified total-fibre theorems; instead
   give distinct names/types and prove the semantic bridge.
2. Revisit the mixed partite step. The previous attempt to reflect
   **undefined** function domains globally is unjustified and
   unnecessary. The key remaining problem is preserving copywise
   embeddings over a reducible projected separator.
3. Separately formalize the full relational closure description U
   and the locally finite completion transfer of Theorem 2.18.
   The previous verified 2019 Theorem 2.19 corollary is already
   available for the general set-valued language; an exact
   single-valued-partial class-preserving formulation is an
   additional worthwhile interface check.
4. For an editorial correction to the 2026 survey, either restore
   genuinely partial functions and their 2019 homomorphism notion,
   or make the positive-domain homomorphism notion explicit for
   the existing nonempty/empty encoding. If one wants to support
   defined-but-empty set-valued fibres, introduce an explicit
   domain predicate instead of conflating it with ∅.

**Editorial caution:** the circulation manuscript is frozen. Attach
`\todo` and validation markers for the distinction, but do not
rewrite its definitions or theorem statements without the authors'
editorial decision.
