# Published Appendix A versus checked Lean constructions (8 October 2026)

## Historical anchor and scope of this audit

Requested reference: a commit referred to as **"zmeny z publikovany verze"**
("changes from published version"). That exact message was **not found** in the
308 commits reachable from the current GitHub survey `main` branch as of this
audit. The oldest available source snapshot on that branch is the
**Initial Overleaf Import**, commit
`6f5fca78fec42577a30f6b551164c114a3384dfe` (1 October 2026).
It is used as the explicit source-diff anchor here rather than inventing a
nonexistent SHA. Confirm against the actual publisher's final TeX before
asserting that it is byte-for-byte identical to the published version.

Source repository:
`janhubicka/Ne-et-il-s-classification-programme-of-Ramsey-classes`,
`main.tex`, Appendix A.3, `thm:tree_invariant`, `thm:sparseningRamsey`.
The survey is already published (Computer Science Review 59 (2026), 100814).
The intention is a **revision** preserving the explanatory partite proof.

## Statement comparison: the key regression

| Dimension | Initial Overleaf import | Current verified circulation text |
|---|---|---|
| `thm:sparseningRamsey` language | Arbitrary finite language with relations and set-valued functions | Relational |
| `A` | Irreducible | Irreducible (formal theorem removes this) |
| `B` | No irreducibility hypothesis | Irreducible |
| Ramsey arrow | Full embeddings | Induced relational embeddings |
| (1) | Full function homomorphism-embedding `C -> C0` | Relational homomorphism-embedding |
| (2) | Genuine closed substructures of at most n **vertices** fully homomorphism-embed into strict function-language B-trees | All relational induced tests at most n, relational strict B-trees |
| (3) | Every irreducible substructure extends into a B-copy | Same for relational irreducibles |

The original *strict* tree definition at `defn:tree-amalgamation` requires
every functional free-gluing root to be contained in an irreducible
substructure of each side. It must not be silently replaced by the older
**loose** tree notion.

Appendix A.2's `thm:inducedpartite` was also narrowed to relational
language in the revision; separately, the full genuine-function EHN
induced construction has now been formalized. The recursive Appendix A.4
retains the function-graph/U-closed approach for intermediate recursive
pictures; **no U-closed pictures are needed in the native EHN iteration**.

## Original proof skeleton and exact Lean counterpart

The original proof has five stages. Keep this organisation when restoring
the theorem.

1. **Induced partite lemma (Hales--Jewett)**: the native function-language
   coordinatewise product and full line embeddings are checked by
   `FunctionalPartite.Induced.partiteLemma`. Functional output
   transversality is indispensable.
2. **Picture step and n-vertex induction**: the actual full-function EHN
   Picture, initial stage and complete pass are checked in
   `EHNWeakAttachmentStep.lean`, `EHNPictureWeakTree.lean`,
   `EHNInitialWeakTree.lean`, `EHNConstructionWeakTree.lean`.
   The checked invariant is for **weak graph tests**, not yet strict full
   function-language target trees. Each full pass raises the vertex bound
   by one.
3. **Small projected image**: if a weak test has support S, its image must
   be `D.weakInduce (p '' S)`, *not* `D.induce (closure(p[S]))`.
   `IsWeakHomomorphismEmbedding.weakImage` and
   `WeakLocallyTreeCompletable.completion_of_small_weakImage` prove the
   exact graph-tree step for `|p[S]| <= n-1`. This solves the original
   *size-counting* issue, but not full function-fibre reflection.
4. **Maximal image / mixed attachment**: genuine closed test pullbacks
   `closedMixed_pullback_card_lt` have strictly smaller closed left,
   right and common substructures. A reducible separator has an EHN
   quotient labelling into A. Independent strict completions of the
   three smaller structures do **not** supply two extensions over the
   same strict B-tree. The conditional
   `HasCommonRootedProjectedHistoryCompletions.glue` and
   `IsFreeAmalgam.finiteBoundedHistoryCompletion_of_relativeMixed`
   package the right conclusion once that **simultaneous relative-root
   completion** is actually constructed. Domain-reflection failure
   prevents replacing an arbitrary reducible quotient root by one full
   A-copy: `IsolatedQuotientBoundary.false_of_domainFailure`.
5. **n passes and final B-extensions**: genuine functional n-pass
   `inducedRamsey_directFunctionalWeakGraph` proves the full Ramsey
   arrow and weak EHN projection, together with weak graph-tree
   local completions. The general function-language counterpart of the
   relational uniform final-support attachment that establishes (3)
   has **not** been proved, and must be kept separate.

A separate local regression in
`Functional/PublishedProjectionObstruction.lean` shows that the
projection of just two disjoint B-copies to a binary-function B is weak
but **not full**: a cross-copy input pair has no source value although
its projected pair has a target value. This explicitly invalidates the
published proof's assertion that the successive original part maps are
full homomorphism-embeddings, independently of the target gluing problem.

The original paper's sentence "let C'' be the structure induced by D on
pi[C']" is only legitimate if `pi[C']` is function-closed; it is not
guaranteed under an EHN weak projection. For the actual weak induction
the correct phrase is "the weak substructure induced by the projected
vertex set". But even a closed test's graph-tree completion cannot be
promoted to a full strict functional tree by syntax alone: the verified
unary two-step-path example proves this.

## Important independent obstruction to the naive strict iteration

The **actual** native coordinatewise power of an explicit seven-vertex
binary-function stage has the staircase domain-incidence matrix

    1 0 0
    1 1 0
    1 1 1

on six selected input vertices. The resulting domain K_{2,2} cannot be
collapsed by a full function homomorphism: its surrounding rows and
columns distinguish the endpoints. Every strict full B-tree of the
three-vertex binary-function hyperedge template is square-free.
The Lean-checked `NativePowerFullObstruction.lean` therefore proves
that the full finite tagged native power has **no strict functional
B-tree completion**. This refutes an *unconditional stability claim for
that power*, not the existence of another canonical Ramsey witness.

This **generic total-fibre power counterexample is now complete under
the hereditary graph-irreducibility hypothesis**. Lean PRs #119,
#121, #134 and #135–#139 verify that the seven-vertex input stage is a
strict full-functional B-tree with EHN part projection; an inherited
binary relation makes the expanded base graph hereditarily
irreducible; and the genuine tagged power has an *exactly twelve-vertex,
function-closed* test with no strict B-tree completion for
**full total-fibre** homomorphisms. The source's added binary relation is inherited
inside the constituent B-copies, **not required to be a global linear
order**. This does NOT refute the original 2019 partial-function
convention: the same ordered twelve-vertex test has a strict one-copy
completion by the restricted EHN part map, proved jointly with the
negative statement in `orderedStaircase_originalPartial_yes_totalFibre_no`.
Do not apply the full-fibre obstruction to the 2019 mixed-step theorem
without first accounting for this categorical distinction.

## Strongest *currently proved* forms (not conjectures)

- **Relational, strict:** `sparseningRamsey_strict_baseIrreducible_all`
  gives all three original conclusions for arbitrary A and
  **irreducible B**, without assumptions about A irreducibility.
- **Relational, loose:** `sparseningRamsey_loose_all` gives all three
  with arbitrary A,B, but the tree target is *loose*.
- **Full function language, graph target:** the genuine native theorem
  `sparseningRamsey_functionalWeakGraph` (new module
  `Functional/PublishedSparseningScope.lean`) removes the
  auxiliary class-membership assumption and A->B non-vacuity case,
  allows n=0, and preserves the original full Ramsey arrow.
  It produces a weak EHN projection to C0 and strict **relational
  B-function-graph** tree completions for every weak test of at most
  n vertices, hence the same graph conclusion for genuine closed
  substructures. Hypotheses: positive function arities and
  `A.graph.HereditarilyIrreducible`. In particular it does *not*
  prove published (1), (2), or (3) verbatim.

For a hereditary free-amalgamation class K containing A and B, the new
  `sparseningRamsey_functionalWeakGraph_inClass` additionally guarantees
  `K C`, without separately assuming that A embeds in B; the no-copy
  case chooses B itself. This is the strongest end-to-end functional
  Ramsey/class-preserving weak-graph conclusion now formalized.

The *published* theorem in arbitrary function languages, with original
full-function (1), strict full-function (2), and (3) simultaneously,
remains open in this Lean development. It should not be given a green
validation marker, and its proof should not be described as complete.

## Recommended restoration approach

**Keep the original five-part exposition**, but use an explicit
functional weak-image invariant when motivating the verified n-pass
construction. Isolate three unresolved obligations before re-stating
the original full sparsening conclusion:

(F1) replace/strengthen the global EHN projection so that it is a **full
homomorphism-embedding** into C0, reflecting function domains;

(F2) construct strict full B-tree completions in the mixed attachment
case with one **common relative target root** and compatible isolated
extensions, avoiding the now-disproved generic strict power invariant;

(F3) perform final class-preserving full B-attachments over **closed**
irreducible roots, without losing the Ramsey arrow, (F1) or the
n-vertex local property (F2).

In the interim, distinguish three theorems rather than redefining the
word "tree": the checked relational strict theorem, the checked native
functional/weak-graph theorem, and a clearly labelled proposed
published-strength functional theorem.

A useful alternate programme is to work first with *loose full-function
trees* (closure-faithful but allowing reducible gluing roots), then seek
a strictification lemma under a natural hypothesis on B and the
attaching histories. This is not a replacement for proving the published
strict statement.
