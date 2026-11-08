# Track D: colliding canonical root labels — precise native frontier (2026-11-08)

**Verification status:** proposed new Lean statements are in draft PR #575 and require an exact-head full build and named-axiom audit. The 2019 survey manuscript stays frozen; this is a non-manuscript mathematical audit.

## What is already kernel-checked

The common separator `R=closedTestPullback(...).common` of an **actual closed native full functional EHN binary attachment** carries the canonical map
```
q : R → A := weakRestrict.part ∘ pb.commonMap
```
and `R.IsEHNHomomorphismEmbedding A q` (`closedTestPullback_common_EHN`). The two full pullback-side embeddings have the **same** original outer projected labels (`closedTestPullback_common_part_compat`).

If `eAB : A ↪ Base`, the actual root **always has an absolute one-copy strict original-partial Base-tree completion** via `eAB ∘ q`, even when q is not injective and R is reducible (`native_closed_separator_originalPartial_oneCopy`). This is *not* a full embedding of R into Base and supplies no relative completion of the two larger sides.

The irreducible EHN collar method of merged PR #570 requires the entire R to embed FULLY inside a source-side irreducible collar and requires that collar's canonical EHN labels to agree with q. Its `irreducibleEHNCollar_rootLabels_injective` theorem implies q must be injective.

## Actual collision branch: draft PR #575

Suppose `x≠y` are actual vertices of R with `q(x)=q(y)`. The proposed native corollaries combine existing checked EHN irreducible-image and finite free-decomposition theorems to show:

- R is **not irreducible**.
- R is **not one-generated**; the automatic one-generated-root completion theorem cannot apply.
- R has an **actual proper full set-valued-function free decomposition** `R = R_L *_{R_0} R_R`, all of whose side/root carriers have strictly fewer vertices than R.
- No irreducible source collar extending the *same* q can contain the entire R.
- Nonetheless, R retains the **absolute** one-copy original-partial Base completion from the checked theorem above.

The source language and defined/undefined function-domain convention are unchanged. No finite weak test is replaced by a generated hull, and the above strict size drop concerns the **separator R**, not the total generator rank of the surrounding Picture.

## Exact remaining target construction

What is **NOT** proved: given the full closed pullback sides `L` and `M` of the same native attachment, with their actual common reducible separator R, construct
```
∃ Start qStart,
  TreeAmalgam Base Start ∧
  HasOriginalPartialTreeExtensionCompletion (Start := Start) Base R→L qStart ∧
  HasOriginalPartialTreeExtensionCompletion (Start := Start) Base R→M qStart.
```
One may take `Start=Base` and the *noninjective* map `eAB∘q` as a candidate, but **the EHN root completion does not imply the two relative extensions**. The already-verified `originalPartialTreeCompletion_glue_relative` combines such extensions *after they exist*. The verified `originalPartialTreeExtension_append` composes the history only once the incoming side has its relative witness over the same previously completed tree.

A strict vertex-count induction on the now-proved proper decomposition of R would have **smaller root pieces**, but its missing proof obligation is to synchronize their relative maps into the *same* strict target extension while preserving every original-published A-copy/history mark on the prior Pictures. It is not legitimate simply to free-amalgamate independently chosen absolute completions, because the gluing roots may not be contained in irreducible target constituents.

The Hales–Jewett **historical parameter sets** are the remaining possible compatibility resource. The verified common-parameter-coordinate retraction route applies only to restricted line families, which are not enough for the Ramsey colouring step. The merged native three-line C7 example rules out a history-free global EHN retraction shortcut; it is not a counterexample to the conditional rank-successor theorem since the correct K2 predecessor locality already fails in its triangular control.

### Next isolated theorem to attempt

**History-compatible reducible-root relative extension:** with `Start` carrying the *already chosen* completion of the original power-core anchor, prove an **incoming old-copy** relative original-partial strict extension over the exact canonical map on R for each selected HJ line, preserving the previous attachment's projected history. The existence of a proper decomposition of R does not yet give the requisite coherent target construction. This step should be proved in English first and adversarially audited before strengthening Lean's conditional schema.

Do not green-mark the unrestricted strict functional n-pass theorem or rewrite the frozen Appendix A manuscript.
