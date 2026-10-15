# Native functional iteration from the verified closed recursive Picture
### Corrected correspondence note — 15 October 2026

**Status:** proof architecture and individually stated formal lemmas, NOT a
claim that the strict functional sparsening theorem is completed.

## 0. The intended theorem and why the earlier detour was wrong

The user-specified target is the *published-order iterated partite argument
in the natural language of partial functions*, with **irreducible closed
base B** (the irreducibility hypothesis on B was inadvertently dropped in
an earlier manuscript revision). Do not substitute the alternative
profile/relational-sparsening/fresh-tag proof of *All Those Ramsey Classes*
for the native iterated functional construction.

The recursive construction in
`PartiteConstruction/Functional/OrderedRecursive.lean` is verified:
`Structure.orderedRamsey` produces an actual Ramsey witness with
genuine set-valued functions. Its ranking-to-singleton reduction,
`rankExpand_singletonValued`, `Embedding.rankExpand` and
`arrow_of_singletonExpansion`, is checked. The temporary semi-closed
relational steps belong only to that **recursive construction**.
The output of that phase is a genuine closed functional Ramsey picture D.
The subsequent iteration should never replay the recursive construction.

For the full native induced pass use the already proved
`FunctionalPartite.EHN.inducedConstruction`,
`FunctionalPartite.EHN.pictureLemma`, the native Hales–Jewett power,
function-closed selected supports, full copied embeddings and free
attachments. Every intermediate **functional** Picture has real
function fibres. Positive arity eliminates empty-overlap hazards;
nullary roots have a separately checked transport mechanism.

The stage projection p to the (closed/genuine) control D is **not** a
full total-fibre homomorphism on all tuples. Source-undefined inputs can
map to defined target inputs, even between two disjoint copies of an
irreducible B. The correct original-2019 partial-function map is
`IsOriginalPartialHomomorphismEmbedding`, equivalent to the native
`IsEHNHomomorphismEmbedding`. A closed control does not by itself
imply reflection of undefined domains. The verified two-copy example
in `PublishedProjectionObstruction.lean` establishes this limitation.

## 1. Weak substructure is the right induction object

For an exact vertex set S of a genuine function structure C, use

    C|ᵂS := C.weakInduce S

with the same vertices and original relations and with function output
sets intersected with S (when using the older encoding in which an
empty fibre means undefined). For the projection p:C→D use

    p_S : C|ᵂS  →  D|ᵂ(p '' S),

never the closure hull of p[S]. Thus `|p[S]| ≤ |S|` exactly as in
the relational proof.

**Already proved:**

* `Structure.weakInduce_graph_rel_iff`: weak function substructures
  are exactly induced graph-incidence relations, on the identical
  vertex set. This is an internal interpretation lemma, not a mandate
  to construct relational Pictures.
* `IsWeakHomomorphismEmbedding.weakImage`: every graph-protected
  map restricts to a graph-protected map of the two exact weak tests.
* `IsEHNHomomorphismEmbedding.graphHomomorphismEmbedding`: native
  functional EHN projections supply the former hypothesis. Its
  proof passes through a closed irreducible hull **only to localize
  an irreducible test**, not to change the tested weak set or rank.
* `IsEHNHomomorphismEmbedding.closedToWeakImage_originalPartial`:
  on a **closed source** S, p induces a genuine original-2019 partial
  function homomorphism-embedding from C|S into D|ᵂp[S].
  Thus at the terminal stage the original closed structures recover
  precisely the expected functional map and strict target can be used.

**New proof obligation / lemma (this branch):** after the
rank-to-singleton reduction, if C is singleton-valued and p is
original-partial, then for **every** S the restricted map
`p_S : C|ᵂS → D|ᵂp[S]` preserves the entire function fibre on
*every input that remains defined in C|ᵂS*. This is
`IsOriginalPartialHomomorphism.weakImage_singleton` in
`Functional/WeakSingletonPartialProjection.lean`.
Combined with the already checked graph protection, the named pair is
`IsEHNHomomorphismEmbedding.weakImage_singleton`.
Only claim kernel certification when this branch's full CI and axiom
checks succeed.

Why singleton fibres matter: for a nonempty weak source fibre
there is a retained value y∈S. Singleton-valuedness forces the
original fibre to be {y}; exact EHN fibre preservation then forces
the whole target fibre to be {p(y)}. Since p(y)∈p[S], weakly
restricting the target changes nothing on that defined tuple.
Undefined source inputs impose **no** target-domain condition.

For arbitrary multivalued fibres, some original outputs may be lost
from S while other vertices of S project to their output labels.
The target weak fibre can then be larger than the image of the
source weak fibre. We must either keep the ranked singleton
representation throughout the induction, or separately prove a
relative output-lifting hypothesis. Do not assume it for all
multivalued stages.

There is a direct way to ensure that the singleton hypothesis remains
true throughout the construction: the already verified
`Structure.originalPartialModelClass_free` gives a genuine free-amalgamation
class of singleton-valued partial-function structures. The existing EHN
`inducedConstruction_allArity` and its n-pass/final-coverage variants are
class-preserving, so specializing them to this class certifies that their
output stages are still singleton-valued. The theorem
`Structure.sparseningRamsey_nativeSingleton_graphStrict_weakProjection`
(added in the same PR, pending CI) packages the complete native n-pass,
B-coverage, and both exact weak-projection laws, with *no* artificially
multivalued intermediate function. Its local tree property is explicitly
still **relational graph strict**, not the missing full-function strict
local completion.

The preceding pair is **not** automatically a full functional
homomorphism-embedding of arbitrary weak substructures: graph
irreducibles and full functional irreducibles need not coincide,
and domain reflection remains intentionally absent. The correct
weak induction invariant comprises source-defined fibre preservation,
graph-level protection, and the specified partial-A-copy/history
data; closed terminal tests are upgraded using the already verified
closed-to-weak-image theorem. This is how weak substructures play
the role of ordinary homomorphism-embeddings on U-closed pieces
without demanding a false full reflection theorem.

### Full embeddings restrict weakly without ANY singleton assumption

`Structure.Embedding.weakRestrictToPreimage` (new proof in this
branch, CI pending) proves directly that for a FULL functional
embedding e:A↪B and an arbitrary exact set S⊆B,

    A|ᵂ(e⁻¹[S])  ↪  B|ᵂS

is again a full **function-language** embedding. Both original
relations and entire retained function fibres are reflected. The
preimage, not a generated closure, is the new source carrier.
This is the elementary mechanism by which the full closed root and
side embeddings in a functional free amalgam restrict to the weak
pieces of a mixed test. It is valid even with multivalued functions.

Do not extend the lemma to a merely weak EHN projection: for that
projection the separate singleton source-defined map and
ambient-closed irreducible protection below are required.

## 1a. The ambient-relative weak HE (precise closed-test bridge)

A weak S may *appear* irreducible only because an original function
output was forgotten. Requiring a full functional embedding of EVERY
such intrinsic weak irreducible into a strict B-tree is false. The
proper projection invariant instead protects **all full irreducible
ambient pieces** E→C whose ranges lie in S. A full E→C has closed
function-image range; its projection must be a full embedding into
the weak target on p[S]. This is precisely the extra clause in

`Structure.IsAmbientWeakOriginalPartialHE C S T f`.

New theorems (PR #319, CI pending):

* `IsEHNHomomorphismEmbedding.ambientWeakImage_singleton`:
  for every weak S, p:C→D induces this ambient-relative weak
  interface to D|ᵂp[S]. No generated hull or target-domain reflection.
* `IsAmbientWeakOriginalPartialHE.toOriginalPartialHE_of_closed`:
  when S is genuinely function-closed in C, this *same* interface
  is a usual original-partial **homomorphism-embedding** of
  the full induced function structure C|S into T.

This realizes the intended phrase “weak substructures do what
normal homomorphism-embeddings do on U-closed structures,” without
making the demonstrably false assertion that every weak test should
fully embed into a strict B-tree. It remains necessary to construct
actual strict B-tree witnesses preserving this predicate through the
mixed Hales–Jewett Picture attachment.

## 2. Published two-case induction, directly in functions

Fix B irreducible and closed, a genuine closed Ramsey control D
from the verified recursive construction, and n≥1. Each native
functional partite pass proceeds over the finite ordered list of
embeddings α_i:A→D. Retain full functional A-, B-embeddings, closed
selected support, and the Ramsey arrow. For a test of size ≤n
in the current stage use C|ᵂS and its exact weak image in D.

1. **Small projected image:** if |p[S]|<n, use the predecessor
   invariant on D|ᵂp[S]. Compose its tree witness with the exact
   weak-image projection, without adding closure vertices.
   Full source-defined fibre equality in the ranked singleton
   case and graph HE are independently available.

2. **Maximal image:** if |p[S]|=|S|=n, p is injective on the test.
   Pure Hales–Jewett-core tests inherit the canonical A-labelled
   completion; pure copied-old-stage tests use the preceding
   invariant. For a mixed test split by the **actual** closed
   support, work with the actual common piece G=E∩F and
   projected histories; do not glue arbitrarily chosen
   completions of E and F over incompatible copies of G.

The strictly functional mixed target remains the difficult step:
construct **two relative extensions of the same strict B-tree
completion of G**. The conditional glue itself is already
verified as `IsFreeAmalgam.originalPartialTreeCompletion_glue_commonTree`
and `originalPartialTreeCompletion_glue_relative`; existence of
compatible witnesses for arbitrary hard multigenerated separators
in *genuine constructed Pictures* is NOT yet established.

Importantly, PR #313 exhibited a C5 obstruction already with
A=B=K2 (irreducible) to a universally quantified arbitrary-stage
mixed-root schema. Restoring B irreducible does not make that
over-strong premise true. The legitimate invariant must remember
the actual HJ core and partial A-copy histories. Do **not** adopt
that false schema as a new axiom. The source-specific initial
projected-history invariant has been merged in #314; the
initial-Picture specialization is green in draft PR #315.

After n genuine functional passes, perform the checked final
B-coverage pass. The complete **weak-graph** conclusion is
`sparseningRamsey_nativeFunctional_graphStrict_withBCover`.
This is **not** the final strict functional B-tree assertion.
Complete the exact native relative-extension lemma and only
then promote its validation marker.

## 3. Defined empty versus undefined

The older survey notation `F:A^r→P(A)` treats an empty fibre
as undefined. That is sufficient for ranked standard partial
single-valued functions and for the existing EHN equivalence,
but cannot distinguish an *originally defined empty-valued
operation* from an undefined operation.

If the general theorem permits such genuinely empty-valued
definitions, use the separate `PartialSetStructure` interface
`F:A^r→Option (Set A)`: `none` is undefined and `some ∅`
is defined-empty. Weak restriction must preserve an original
`some ∅` and turn a `some T` with T≠∅ and T∩S=∅ into
`none`. The exact weak projection lemma needs its analog in
this enriched language; it is not a reason to abandon the
functional iteration.

PR #318 is building this extension separately; at the most
recent inspected head, its previous Lean CI failed on small
proof elaboration errors, so do not claim it is merged/checked.

## 4. Match with the verified All Those Ramsey Classes proof

The corrected relational theorem
`coordinated2019_ramsey_by_profile_sparsening` is completely
verified, but its internal **alternative** proof avoids the
native rank increment via profiles, relational sparsening and a
second tagged closed Picture. It is a useful correctness oracle:
the exact original C0 and n stay fixed; weak S is never replaced
by a closed hull; compatible common boundaries cannot be chosen
independently; and B-copywise transfer suffices at the end.

For this survey appendix we use the directly verified native
function construction and the published order: initial Picture,
HJ Picture steps, weak-test two-case induction, n passes, and
final B-copy extension. The relational alternative is not a
replacement algorithm.

### Working acceptance tests

* Input/output stages have genuine (ranked) functions, with no
  broken semi-closed intermediate language in the iteration.
* B is irreducible (and each B-copy is a closed embedded copy).
* The projection law on defined weak fibres is verified, not
  conflated with reflection of undefined inputs.
* S and p[S] stay exact vertex sets in both cases.
* For the hard mixed case, obtain one common strict B-tree root
  and actual relative side extensions, keeping the projected
  partial-A history. Merely quoting the conditional glue or
  the false uniform hard-root schema fails the test.
* Complete n iterations and final B-coverage, then certify the
  precise strict function-language theorem with an axiom audit.
