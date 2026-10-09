# Strict functional tree targets: reduced proof obligation (8 October 2026)

> **Scope correction (9 October 2026).** This file records a *conditional*
> attempt to obtain strict B-tree targets while preserving **all** function
> fibres on every tuple, including empty fibres. Such a generic invariant
> is now **disproved** for the actual tagged native Hales--Jewett power:
> the exact 12-vertex closed test persists with a hereditarily
> irreducible graph-base; see `native-functional-power-obstruction.md`
> and the axiom-checked `NativePowerOrderedTwelve.lean`.
> This does **not** refute the original 2019 theory: its partial-function
> homomorphism-embeddings preserve fibres only on defined source tuples,
> and the *same* test has a strict one-copy completion in that sense.
> Future strict-root arguments intended for the 2019 theorem should use
> `IsOriginalPartialHomomorphismEmbedding` and must not require
> reflection of missing source function domains. The verified weak
> graph-tree induction remains unchanged.
>
**Status:** research/verification note, not an additional Lean theorem. The
printed relational Appendix A and the verified direct native n-pass theorem
remain unchanged. Do not mark any strict full-function iteration proved.

## What is established

The native positive-arity EHN iteration is complete at the *weak graph-tree*
level: `Structure.inducedRamsey_directFunctionalWeakGraph` (#104, axiom audit
green) preserves the full function-language Ramsey arrow and class membership
and raises the bound for arbitrary weak **vertex** tests from n-1 to n.
`inducedRamsey_directFunctional_closedGraphTests` (#106) applies this conclusion
to genuine closed substructures with the **same** vertex bound.

`FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion`
(#109, axiom audit green) shows the missing full-tree transfer is mathematical,
not a type mismatch. For unary F, B is the single edge 0 -> 1. The relational
B-tree obtained by identifying the first edge's output with the second edge's
input is a two-step directed path; its *whole source* is function-closed, but
every genuine full-functional B-tree satisfies F(F(x)) = empty. Hence there is
no full functional homomorphism from the path into a full B-tree. In
particular, source closedness is insufficient to repair a nonclosed *target*
gluing root. The example is **not** a counterexample to a native-EHN-specific
strict theorem.

The direct construction uses **genuine functions** throughout. It does *not*
require U-closed relational pictures; these belong to the separate recursive
construction, in whose intermediate stages the function structure may be
broken.

## Correction: the projected image of a weak test is weak too

For **every** vertex set S in a native functional stage C and its EHN
projection p:C -> D, the correct source and projected target in the
n-vertex induction are

    C.weakInduce S             and             D.weakInduce (p '' S).

The target function fibre over a tuple from p[S] is exactly its full
D-fibre intersected with p[S]. We do **not** generate a function-closed
substructure of D on p[S], and do **not** enlarge the image to a closure
hull. Both weak graph encodings are precisely ordinary relational induced
structures. The restricted map p|S is a **weak graph**
homomorphism-embedding into this weak target, not in general a full
homomorphism in the original function language.

In particular, even if S is a genuinely *closed* source substructure, p[S]
need not be closed in D under a merely weak EHN projection (multi-input
function domains can fail to reflect). The positive assertion of #111
that p[S] is closed is **conditional** on the extra assumption that p|S
is a full function homomorphism-embedding. It must never be substituted
for the general weak-image step.

The exact weak-image factorization is formalized as
`IsWeakHomomorphismEmbedding.weakImage` in
`Functional/ProjectedWeakImage.lean`. The corresponding small-image
graph-tree statement is
`WeakLocallyTreeCompletable.completion_of_small_weakImage`:
if |p[S]| <= m, a level-m weak-tree witness of D completes C|^w S
at **graph-tree level**, using D|^w p[S]. This does not imply a
strict full-function B-tree completion for the weak test.

There is therefore no additional root/gluing closure condition needed
merely to **form the weak image**. Root closure belongs to the distinct
strict *target tree* problem, not to the source/image vertex-size count.

## A useful exact reduction: failures of domain reflection

The following assertions are already Lean-proved in
`Functional/FibreExactness.lean`:

* `IsEHNHomomorphismEmbedding.map_func_of_nonempty`: for an EHN projection
  p:C -> D, every function symbol F and input tuple x with F_C(x) nonempty,
  p[F_C(x)] = F_D(p x).
* `IsEHNHomomorphismEmbedding.isHomomorphism_of_domainReflection`: p is a
  full homomorphism if it additionally reflects the *nonemptiness* of all
  function fibres.
* `IsEHNHomomorphismEmbedding.inputHull_reducible_of_domainFailure`: if
  F_D(p x) is nonempty but F_C(x) is empty, the closed hull generated by
  the input tuple x admits a proper *full-functional* free decomposition.

Thus there is **no independent multiplicity/choice of outputs problem** for
an EHN projection on a defined input. The only potential fibre defect is
domain reflection, and every defect has a reducible input hull. This is an
argument about EHN projections, **not** about arbitrary graph completion maps
and **not** about target gluing roots.

### Checked small-image full-functional transfer lemma (PR #111)

Let p:C -> D be EHN, S a finite **closed** vertex set of C. Assume the
restricted map p|S reflects nonempty function domains:

    for each F and x in S^arity(F),
    F_D(p x) != empty  ==>  F_(C|S)(x) != empty.

Then:
1. `restrictClosed_toFull_of_domainReflection` makes
   C|S -> D a full functional homomorphism-embedding.
2. **The projected image p[S] is function-closed in D**: for inputs in p[S],
   choose preimages in S; fullness supplies a preimage of every target output,
   and closedness of S keeps it in S.
3. Consequently C|S -> D|p[S] is full, and *if* D has strict full-functional
   B-tree completions for closed tests with |p[S]| <= m, C|S has such a
   completion too, by composition. No injectivity of p and no closure hull of
   the tested S are required.

The full pullback, including image closedness, local full map on the image
and final composition into the strict target tree, is checked in
`Functional/ProjectedClosedTreePullback.lean`:
`LocallyClosedTreeCompletable.pullback_localFull_closedImage` and
`LocallyClosedTreeCompletable.pullback_EHN_closedImage_of_domainReflection`.
The full build and theorem-axiom check passed on proof commit
`2839ba4560364d0293002244c6c6be0413c45923`
(workflow `37745840826`). This covers the `|p[S]| <= n-1` case in an n-pass
**strict** induction *when* the restricted projection reflects domains.
Without that hypothesis it does not address even this case.

**Unary case:** `UnaryEHNCompletion.lean` proves
`IsEHNHomomorphismEmbedding.toFull_of_unary`. Hence the additional
domain-reflection hypothesis is automatic for unary functions, regardless
of the source fibre; the transfer just described applies to every closed
S in that case. Furthermore, when its *control* A itself embeds in B,
`LocallyGeneratedTreeCompletable.of_ehn_unary` gives a one-copy full B
completion of the entire EHN source. This does NOT solve final native
iteration, since the original Ramsey witness D generally does not embed
in B.

## The actual remaining mixed-root lemma

For one **native full-functional EHN binary attachment**, let S be a
function-closed finite test on at most n vertices, and let
R -> E, R -> H be its full-functional pullback over the selected closed
support. In a genuinely mixed test, the sizes of E, H and R are all
strictly smaller than |S|; this is checked as
`FunctionalPartite.Attachment.closedMixed_pullback_card_lt`.

The common R carries an EHN projection into the selected A, and the checked
dichotomy `closedTestPullback_common_embedding_or_decompose` says that either
R fully embeds in A with its prescribed labels, or R properly decomposes
as a full-functional free amalgam.

* **Embedded/irreducible root:** the verified relative-history completion
  and `FunctionalRelativeHistoryTreeLike.glueWholeWitnesses` give compatible
  labelled side completions; full B-tree gluing with isolation is checked.
* **Reducible root (OPEN):** from completions of the three smaller structures
  R, E, H, construct ONE strict full B-tree `Start`, a common map
  q:R -> Start, and *both* relative full B-tree extensions of E and H over
  Start, respecting (a) the same projected-history diary and (b) exact
  root isolation. These witnesses must be chosen simultaneously. Choosing
  independent full-tree completions of R, E and H does **not** imply this
  compatibility. The conditional induction and glue have already been proved
  as `IsFreeAmalgam.finiteBoundedHistoryCompletion_of_relativeMixed` and
  `HasTreeExtensionProjectedHistoryCompletion.glue_relative`.

This is the exact next nontrivial theorem, not a missing cardinal estimate.
A proof by induction merely on the number of vertices of R is *not*
automatic: splitting R does not necessarily split E or H in the same way.
Any claimed reduction of this step must explicitly produce common relative
extensions and prove they remain isolated after replay/merging.

A successful strict functional n-pass induction should maintain a
closure- and domain-aware **relative root certificate**, rather than
attempting to convert an arbitrary completed relational graph tree at the end.

## Routes, from least to most ambitious

1. **Finish the unary/domain-reflecting projection case first.**
   Prove the small-image transfer above. Then investigate an A-labelled
   relative witness for a common R whose map to A is a *full*
   homomorphism-embedding rather than necessarily an embedding. A full
   map makes the projected image of each closed R closed; it does **not**
   automatically produce the isolated relative extension. Verify that
   isolation, and keep the genuine source size bound.

2. **Full mixed-root induction with simultaneous witnesses.**
   Strengthen the side invariant by retaining one common strict root tree,
   two isolated relative extensions, and finite projected and source
   histories. Use the checked proper free decomposition of R to generate a
   relative witness for that shared root, *not* three independent witnesses.
   The missing lemma is the existence of these compatible relative
   extensions in the reducible-root branch.

3. **Target-closure certificate on graph witnesses.**
   Independently strengthen the direct graph-tree witnesses to have
   function-closed gluing roots and a closed embedding of each closed
   source test. The decoding theorem
   `RelStructure.FunctionClosedLocallyTreeCompletable.toFunctional`
   is already checked. Merely adding closedness of the source does
   not imply the strengthened graph witness (#109).

4. **Use an already verified weaker endpoint if that suffices.**
   `inducedRamsey_directFunctional_closedGraphTests` gives the
   native Ramsey/class-preserving conclusion and closed-test graph B-trees
   without any more work; the separate
   `IsEHNHomomorphismEmbedding.locallyClosedLooseTreeEmbeddable`
   gives genuine *loose* functional B-trees but drops strict root
   containment. Neither should be relabelled a strict functional
   sparsening theorem.

## Formalization and editorial safeguards

- Keep `A.graph.HereditarilyIrreducible`, positive function arities and
  the actual hypotheses of #104 visible; do not silently replace by a
  weaker assumption.
- Count `|S|` for arbitrary weak substructures; never replace it by
  `|closure(S)|`. All proposals above only add target witness data.
- Keep the distinction between the global weak EHN projection, a full
  local completion map, and a target function-closed gluing root.
- Do not modify the frozen circulation text of the survey. New hypotheses
  and unproved branches belong in optional TODOs, not green Lean markers.
- For new Lean work, reuse the now-checked small-image transfer; then
  test the reducible-root relative witness on finite unary examples
  and on the existing two-step-path regression before claiming a
  general result.
