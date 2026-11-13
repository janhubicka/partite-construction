# Track D — English proof first: genuine native closed mixed attachment, absolute strict target

**12 November 2026.** Stacked on English-first parent PR #637 (which
derives compatible, possibly colliding marked target sides from the
ordinary control predecessor, rather than assuming them). This note
is for the source repository only. Frozen numbered survey Appendix A
and collaborator TODOs remain unchanged.

## Exact native theorem

Let B be an actual finite functional partite system over a fixed full
control D, and let α:A↪D be a selected FULL embedding. Put
Supp = B.support(α) and let E be a genuine partite system over the
SAME D with a full part-preserving support attachment f:B|Supp↪E.
Form the **actual native full** one-copy attachment

    Whole := UnitAttachD B Supp hSupp E f.

Let S be a literal finite **function-closed** test in Whole,
|S|≤m+1. Suppose it is genuinely mixed: it contains an actual vertex
outside the core E-copy and an actual vertex outside the newly
attached B-copy. No weak tested set is replaced by its closure.

Assume the ORDINARY rank-m ambient-relative strict B-tree predecessor
for the fixed control D:

    SetAmbientRelativeWeakTreeWitness.AtMost A Base D id m.

This is a hypothesis about exact weak control tests and arbitrary
finite history lists; it has no globally protected A-mark premise.
Then the full induced exact source test Whole|S has an **ABSOLUTE
strict full-functional Base-tree completion by an ORIGINAL-2019
source-defined partial homomorphism-embedding**.

The common separator's canonical map into A is allowed to collapse
distinct vertices. We assume neither root irreducibility, root
generator bounds, closed projected control images, full reflection
of source-undefined function domains, nor any target-side
relative-completion oracle.

## Proof against genuine existing Lean data

The checked `closedTestPullback` of S produces a FULL native
source free diagram

    R -> L, R -> M, L -> Whole|S, M -> Whole|S,

where L is the exact closed tested core preimage, M the exact
closed tested old-copy preimage, and R their FULL common separator.
The verified `closedMixed_pullback_card_lt` gives

    |L| < |S| <= m+1,  |M| < |S| <= m+1.

Hence |L|,|M|≤m. In particular the exact projected vertex images
I_L = E.part[L] and I_M = B.part[M] are also of size ≤m.
This charges ONLY ACTUAL vertices of the original closed test S,
never the potentially larger closure of a weak image or a
diagnostic function-input hull.

The closed source side maps `L↪E` and `M↪B` are full; composing
with the genuine EHN part maps `E.part:E→D` and `B.part:B→D`
gives EHN maps `p_L:L→D`, `p_M:M→D`.
The checked `closedTestPullback_common_part_compat` gives a SINGLE
canonical (possibly noninjective) `q:R→A` satisfying

    p_L(s_L r) = α(qr) = p_M(s_M r).

Invoke the exact source-side result of PR #637
`originalPartialTreeCompletion_of_ordinaryControlRank` on this
literal pulled-back full free diagram. The ordinary rank-m control
predecessor supplies strict B-tree witnesses for I_L,I_M.
The selected ambient α-copy certificates in those witnesses
supply full TARGET A marks on all OCCUPIED root labels; exact EHN
pullback and closed-side conversion yield original-partial side HEs.
The verified noninjective-mark theorem of PR #635 then glues the
two target trees over the FULL A-marks to give an **ABSOLUTE**
strict functional B-tree completion of Whole|S.

This is a genuine consequence of the stated predecessor and mixed
geometry, with NO new relative-existence oracle.

## Adversarial rejection of stronger claims

1. **Not the full native HJ rank successor.** After gluing the target
   A marks, source vertices in opposite sides with different control
   labels can be identified via *unoccupied* A-mark positions.
   The absolute original-2019 HE permits those identifications.
   They may invalidate `SetRespectsProjectedHistory` and therefore
   the next stage's ordinary predecessor invariant. Thus this
   theorem CANNOT be iterated alone to obtain the full n-pass
   functional statement.

2. **Exact one-copy scope.** This is one true full native
   `UnitAttachD` binary attachment, not a global retraction for
   the entire ordered family of Hales–Jewett parameter lines.
   An individual closed test in any stage can be decomposed this
   way, but the history invariant needed for successive stages
   is still open.

3. **Nonclosed projected boundary.** We do NOT assert that the
   projected I_L or I_M is function-closed. This is the precise
   improvement over the previously checked
   `weakTree_of_closedProjected_alpha_mixed_succ`
   and `weakTree_of_closedOccupied_alpha_sides` — at the cost
   of weakening the conclusion to ABSOLUTE completion only.

4. **No total-fibre smuggling.** Function fibres are preserved
   completely at SOURCE-DEFINED inputs only. The native Set
   presentation uses empty=undefined; genuine defined-empty
   Option(Set) remains a separate dictionary problem.

5. **What is still genuinely critical.** The missing mathematical
   task is to preserve projected-history/ambient-copy certificates
   through the mixed step by controlling false A-mark hits,
   possibly via test-dependent closure profiles. The verified
   2019 two-pass relational closure-profile construction avoids
   this stronger native strict-target rank invariant and remains
   a correct alternative route to the printed survey theorem.

## Lean acceptance

After this English proof, add a single named specialized Lean theorem
`closedTest_originalPartial_weakRankSucc_absolute_mixed`, using ONLY:
- `closedMixed_pullback_card_lt`,
- `closedTestPullback_common_part_compat`,
- exact EHN compositionality of full sides, and
- parent `originalPartialTreeCompletion_of_ordinaryControlRank`.

Run its named `#print axioms` test, full umbrella build and
source/no-admissions audit. Do not mark the history-preserving
iteration verified.
