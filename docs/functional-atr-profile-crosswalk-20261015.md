# Functional sparsening versus the verified 2019 relational theorem
### Proof crosswalk and semantic audit — 15 October 2026

**Status: mathematical correspondence / proof plan, not a new Lean theorem.**
The verified reference is
`AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening`
in `janhubicka/lean-all-those-ramsey-classes`, and its exact English proof is
`docs/coordinated-profile-proof-20261013.md` in that repository.
The present native strict functional n-pass theorem is **conditional** on a
mixed-root extension schema; the uniform arbitrary-stage schema is too strong
(the graph `C5` audit, partite-construction PR #313). We should not solve
the native iteration by assuming that false schema. The proven relational
theorem takes a different route: *profile records → ordinary relational
sparsening → fresh-tagged second closed Picture → exact weak tests*.

## 1. Function semantics come first

The new work-in-progress `PartialSetStructure` (PR #318) represents
a genuinely partial set-valued function as
`F : V^r → Option (Set V)`. This distinguishes:

* `none`: undefined input;
* `some ∅`: defined, empty-valued input;
* `some T` with `T.Nonempty`: defined input with outputs.

A **source-defined partial homomorphism** sends every `some T` to
`some (f '' T)`, including `some ∅`, but makes no assertion on
source `none`. A total-fibre/domain-reflecting homomorphism makes the
same equality on *all* inputs. Neither should be interchanged with
positive preservation of output incidences.

For an exact vertex set `S`, the intended **weak** value is:

```text
none           ↦ none
some ∅         ↦ some ∅
some T, T≠∅    ↦ some (T∩S) if T∩S≠∅, otherwise none.
```

It does NOT enlarge `S` to its function closure. On function-closed
sets the weak restriction agrees with the full induced functional
substructure. PR #318 has the elementary definitions, but its then-current
full CI build was red at the time of this audit, so no fresh validation
marker should be issued for these new declarations.

### Two relational presentations have DIFFERENT uses

The `Dom_F` plus `Graph_F` presentation in
`PartialSetFunctionsDomainGraph.lean` retains full domain information,
but **does not commute with weak induced substructures**: if
`F(x)=some {y}` and `S={x}` with `y∉S`, the weak operation on `S`
is undefined, whereas relational induction retains `Dom_F(x)`.

For the ordinary **relational sparsening of exact weak vertex tests**,
use instead the two predicates

```text
Empty_F(x)    ↔ F(x) = some ∅
Graph_F(x,y)  ↔ ∃T, F(x) = some T ∧ y∈T .
```

These two predicates together are lossless: nonempty graph fibres give
`some` of the fibre, `Empty_F` gives `some ∅`, and neither gives
`none`. They also commute *exactly* with weak restriction:

```text
weakGraph(A.weakInduce S) = (weakGraph A).induce S
```

on the subtype carrier `S`, for each original relation, `Empty_F`
and `Graph_F`. **This exact theorem is proposed, not yet checked
in Lean.** The case split is `none`, `some ∅`, and `some T` according
to whether `T∩S` is empty.

### Morphism bridges that must be kept explicit

1. For a full functional embedding `f : A ↪ B`, the induced map
   on `Empty+Graph` relationalizations is a full relational embedding
   and the image `f[A]` is closed under *all* target outputs.
   Conversely, a full relational embedding **together with function-closed
   range** is a full functional embedding: range closure rules out extra
   target outputs outside the range; `Graph_F` reflection rules out
   extra outputs inside; `Empty_F` detects the empty/undefined cases.
   The range-closed hypothesis is indispensable.

2. A source-defined functional homomorphism induces a positive
   `Empty+Graph` relational homomorphism. The converse requires a
   **fibre-surjectivity clause**: for each source-defined nonempty
   `F_A(x)=some T`, every target output of `F_B(fx)` is in `f[T]`.
   Positive graph preservation proves only the opposite inclusion.
   For ordinary partial **single-valued** functions with singleton-or-
   undefined target values, fibre-surjectivity is automatic when the
   source is defined; **not** for general multivalued functions.

3. Ordinary relational homomorphism-embeddings protect relational
   irreducible tests. This is NOT by itself the stronger original
   partial-function homomorphism-embedding; the fibre equality above
   is an independent obligation, and function-closed protected tests
   must be identified explicitly.

These are intended interfaces and proofs to formalize; no converse
from an arbitrary positive `domainGraph` homomorphism has been asserted.

## 2. Step-by-step crosswalk against the *actual proved* theorem

| Verified relational component | Functional proof counterpart | Audit status |
| --- | --- | --- |
| Fix `C0` via ambient Ramsey and choose `n(B,C0)` once; unrestricted closed Picture `InducedClosed2019UnrestrictedInitial` | Keep the same original control, cutoff, exact arrow and class assumptions. Existing native EHN passes prove a different, free-amalgamation-oriented interface; do not silently assume they prove the unrestricted `K` case. | Relational proved; general functional transfer needed |
| `GeneratedClosureProfiles2019.lean`: `closureProfileExpansion2019`, `closureProfileEmbedding2019` | A profile is an actual **function-closed** induced substructure `H⊆B` and a tuple of generators. Add a relation recording full realizations of `H`. Full embeddings reflect a record because their ranges are function-closed, so the realization of all generators forces the whole `H` into the range. | Relational proved; direct functional closure-range lemma needed |
| `GeneratedClosureProfileBoundary2019.lean`: `closureProfile2019_common_weak_root_closed_boundary` | Enumerate an **exact** weak common root in the profiled language. Its shared profile determines **one** closed `H` in `B` with compatible full embeddings into both completed sides. No independent root choices, no generic arbitrary-stage hard-root lemma. | Relational proved; transfer to function embeddings needed |
| `ProfileStrictTreeCompletion2019.lean`: `closureProfile2019_tree_completion_to_K` | Complete strict trees of profiled `B`-copies using strong amalgamation in `K` over the generated full closed boundary `H`. The root itself need not be closed and the finite source stays vertex-exact. | Relational proved; functional boundary/gluing interface needed |
| `PartiteConstruction.Iterated.SparseningStrictBaseIrreducible`: `sparseningRamsey_strict_baseIrreducible_all` | Apply the **already verified purely relational** sparsening theorem to the profiled `Empty+Graph` language, with the **same** bound `n`. Every exact subset of `B+` is relationally irreducible because its generators have a profile tuple. No native generating-rank increment is required. | Reuse theorem literally after embedding/arrow bridge |
| `ProfileRootTagLanguage2019`, `ProfileRootTagClosedness2019`, `ProfileRootTagLocalLaws2019` | The sparse relational witness cannot simply be decoded as a closed function structure. A second, fresh **full root-pattern-tagged** closed Picture must reconstruct the intended function domains and fibres, validate root/tuple normality, and protect closed function tests. Defined-empty and nullary cases must be covered separately. | Main NEW mathematical/Lean transfer obligation |
| `ProfileRootTagTransfer2019.lean`: `profileTag2019_original_closed_and_coverage`, `profileRootTag2019_forget_arrow` | Recover the actual function language and Ramsey arrow using canonical lifts of embeddings between closed `A,B`. Projected maps must be proved **original-partial fibre-exact**, not merely positive graph maps. | Fibre-exactness is nonautomatic for multivalued functions |
| `Coordinated2019ProfileSparseWitness.lean`: exact `S`, `T=p[S]`, `card T ≤ card S ≤ n`, tree completion to `K`; then copywise Ramsey transfer | Test **every original weak subset `S` of cardinality ≤ n**, not its closure; project to **exact** weak image, use relational tree and constructed closed `K` boundary, upgrade to the required protected functional completion, and apply the SAME local cutoff. | Relational proved; functional last upgrade still needed |

### Quantifiers and hypotheses to preserve

* The original `C0` need not be closed.
* Choose `n=n(B,C0)` **before** either sparse/closed construction,
  and never change it.
* The small tests are **all exact original weak subsets** on at most `n`
  vertices, not enlarged hulls or only intrinsically closed ones.
* The local completion should be a `K`-target preserving selected
  full `B`-copies; it need not reflect every global `A`-copy.
* The general theorem assumes **finite strong amalgamation**, not
  free amalgamation of all target `K`-structures.
* Corrected closed-irreducible membership/protection clauses in
  the reference theorem are intentional and must not be weakened or
  broadened by an informal translation.

## 3. Why a naïve literal reduction is not yet enough

* Ordinary `Dom+Graph` induction does not produce the functional
  weak substructure. Use the `Empty+Graph` presentation for the
  exact weak-test stage.
* Graph-positive maps do not preserve complete multivalued fibres.
  Even `Empty+Graph` maps require fibre-surjectivity or a stronger
  generated-closure/typed-tag argument.
* `Empty+Graph` relations alone do not automatically define a 2019
  `U`-closure description with one **unique complete closure tuple**
  above every root: `Graph_F` has one incidence for each output.
  In particular, a defined-empty value adds no output vertex.
  Reusing the **architecture** is justified; applying the full ATR
  class theorem directly to this graph encoding is **not** justified
  without a separately proved closure-description bridge.
* Ordered enumeration of a finite output set into singleton selectors
  can help for **closed/full** structures, but is not automatically
  functorial on arbitrary weak subsets: deleting the least output
  shifts selector indices. Therefore it is not a substitute for the
  exact weak-induced theorem.
* The verified relational proof **avoids** the original native
  Lemma 2.30 rank increment. A demand for literal lemma-by-lemma
  equality with the *published rank proof* would be stronger than
  the already verified result and would revive the C5 obstacle.

## 4. Shortest trustworthy formalization sequence

1. Repair and finish CI/axiom checks for PR #318's separate
   `Option (Set)` foundation. As inspected on 15 October, its
   Lean job failed in `PartialSetFunctionsClosed.lean` (unknown
   `hNonempty`, tuple-variable elaboration errors); no CI-green claim.
2. Add `PartialSetFunctionsWeakGraph.lean`: `Empty+Graph` encoding,
   explicit weak-induced commutation, range-closed full embedding
   equivalence, and source-defined map/fibre-surjectivity equivalence.
   Include counterexamples for `Dom+Graph` weak-induction and
   `Graph`-only fibre exactness.
3. Reuse the **relational** theorem to construct profiled strict
   trees and closed common boundaries. Port only its closure-range
   and profile-record lemmas to the function API; do NOT recreate
   native n-pass/rank machinery.
4. Prove a function-valued version of the **fresh root-tagged second
   closed Picture** and the exact upgrade from positive incidence
   maps to original-partial fibre-exact maps. This is the real bridge.
5. Assemble the final exact weak-`S`, same-`n` `K`-completion and
   arrow transfer, and only then add a validation marker to the survey.

The intended final argument can be written in natural function-language
notation even when the middle sparsening pass internally uses the
verified relational library. That is a proof of the same **construction
architecture**, not a claim that the currently conditional native
strict n-pass theorem has already become unconditional.
