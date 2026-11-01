# Track D — strict native functional B-trees: history-dependent frontier (2026-11-01)

**Status:** partial Lean advance, **not** a proof of strict functional sparsening. The survey's manuscript text stays frozen; this branch changes only the public Lean library, root-level axiom checks, and this non-manuscript research note. Do not add a green manuscript marker until the exact-head CI and named theorem-axiom checks pass.

## Evidence inspected on main `0959f4d5b857059937a236c77d8cef67cfcdf4e1`

1. `EHNNativeOriginalPartialMaximalMixedReduction.lean`: the actual native free-attachment induction has three branches: pure core/old tests, lower projected generator rank handled by the predecessor invariant, and **maximal projected rank** genuinely mixed exact closed tests needing *two* compatible original-partial strict target extensions over the **same** closed source separator.
2. `EHNMaximalMixedHardRootReduction.lean` and `EHNOriginalPartialMaximalMixedFromTwo.lean`: only mixed tests of generator rank `n >= 2` and common separator requiring **at least two generators** are left. Generator count is not cardinality of the function-generated closure.
3. `EHNOriginalPartialHardRootSchema.lean`: `MaximalMixedHardRootSchemaFromTwo` quantifies over ALL intermediate stages. It is **not** the correct new lemma to prove: `MaximalHardRootC5NativeAttachment.lean` and `MaximalHardRootC5GeneratorRank.lean` already exhibit an exact closed five-cycle of maximal rank in one actual native *arbitrary-stage* attachment. The full stage-level counterexample (local rank, `Stage` class) is not yet kernel-certified. This obstructs promoting the universal conditional n-pass theorem into an unconditional one.
4. `EHNPowerCanonicalRootOneSided.lean`, `EHNPowerCanonicalAnchoredRoot.lean`, and `OriginalPartialRelativeAppend.lean`: the true Hales–Jewett core has a canonical `A -> Base` label root map. The core side's relative completion is proved; the **old-side** prescribed relative completion and its compatibility with *earlier* attachments remain open. Repeated free amalgamation of independently chosen absolute target trees is invalid.
5. `EHNLineOnlyPicture.lean`, `EHNLineOnlyProjectedCover.lean`, and `EHNLineAttachmentStrictWeakLocality.lean`: genuine HJ line-only attachments preserve the ordinary Ramsey Picture and projected irreducible B coverage. A *single* line attachment additionally preserves the strict exact weak-history witness by an EHN retraction. This does **not** prove the same for a list of different lines.

## New verified-*candidate* mathematical interfaces in this branch

- `Functional/EHNSelectedPowerC5Exclusion.lean` isolates a precise history test. The selected `A=K2` support has only part labels `{0,3}`. Every vertex of an ACTUAL selected coordinatewise power, relabelled along that placement, still has part 0 or 3. The previously chosen C5 core has an essential vertex in part 1. The new theorem rules out **any part-preserving vertex map** from that C5 core to a genuine selected power. It is stronger than merely observing that the two core graphs have different numbers of vertices, but it is not a positive strict-completion theorem.
- `Functional/EHNPartPreservingRetractAppend.lean` isolates the *composable* positive binary attachment step: if the current Picture core admits an EHN shadow `q: Current -> Old` preserving the ORIGINAL control parts and the next attaching support map `f` satisfies **`q(f(x)) = x` on the whole function-closed support**, then the actual native one-copy full functional free attachment has an EHN retraction to Old extending `q` on the retained core and acting as identity on the new Old copy. It still preserves all transversal set-valued functions. The finite `n`-vertex exact weak-history invariant follows by the already checked `AtMost.pullback_ehn_commutingParts` lemma, with NO closure or rank inflation.
- `CheckEHNPartPreservingRetractAppend.lean` and `CheckEHNSelectedPowerC5Exclusion.lean` contain named `#print axioms` tests; they must pass exact-head CI before being called green.

**Scope:** a single HJ line has `q(f(x))=x` by evaluation at *one* parameter coordinate (the existing checked `lineUnitAttachment_EHN_retraction`). For a series of lines sharing a common parameter coordinate, evaluation gives a plausible reusable common shadow. For unrelated lines, the pointwise splitting hypothesis can fail; the theorem above does not assert it. This avoids a false global EHN retraction.

## New finite-HJ-history propagation and its sharp limit

The additional full-functional Lean modules
`Functional/EHNPartPreservingRetractFamily.lean` and
`Functional/EHNCommonParameterLineFamily.lean` upgrade the one-step
retraction to an ACTUALLY CONSTRUCTED finite sequence of native full
attachments. The family theorem is conditional only on a pointwise
splitting condition `q0(map_i(x)) = x` for EVERY selected full
support map in the list, and preserves the common old shadow, core
embedding, and part labels. It then pulls back the exact n-vertex
strict weak-history witness with the SAME rank bound.

In the true coordinatewise Hales--Jewett power, if all listed line
symbols have `.parameter` at the SAME coordinate `j`, taking
`q0(z) = z.coord j` gives the splitting condition, by the previously
checked full functional line-map equation. Therefore
`EHN.lineFamily_commonParameter_strictWeakHistory` is a positive
history-sensitive original-function-language theorem, not merely
a proposed proof strategy.

The new `EHN.fixedParameterCoordinate_not_monochromatic` records
an important adverse fact. Such a common-parameter-only family is
INSUFFICIENT for the HJ colouring argument whenever the letter
alphabet has two distinct elements: colour every word by its letter
at `j`, and every line with parameter symbol at `j` is
non-monochromatic. The full Picture must coordinate different
parameter sets; it cannot get both Ramsey and strict locality simply
by restricting all lines to one fixed coordinate.

All three named family/check theorems are included in new root-level
`Check*.lean` files. The full build and axiom-check status must be
taken from the latest CI head, not from an earlier successful run.

## Adversarial seven-cycle check

The full, real tagged line-only Picture may contain a closed induced `C7` even though the old `P5` and HJ power core are forests. The explicit three lines at length 2 are `(b,p)`, `(p,a)`, `(p,p)`; `checks/native_hj_line_only_seven_cycle.py` tests lengths 2–5 and the accompanying note proves the same cycle survives all lengths >=2. Thus **merely attaching every genuine HJ line** does not imply strict `K2`-tree locality on all exact weak 7-vertex tests.

One previously written sentence in that note was wrong: **unordered `A=B=K2` and `D=K3` do not have a Ramsey arrow under colourings of embeddings**. Colour an edge embedding by the orientation induced by an arbitrary external vertex ordering; each edge's two embeddings receive opposite colours. This branch corrects the non-manuscript note. In any case `D=K3` lacks the rank-6 strict predecessor tree invariant, so this C7 does not by itself refute a correctly formulated rank-successor lemma. It instead rejects the history-free line-by-line `Q`-preservation shortcut.

## Exact remaining proof request

The productive target is **history-restricted** relative completion. Fix an ACTUAL stage obtained from the selected HJ power by its ordered list of full support embeddings, and a maximal mixed exact closed test `T` of generator rank `n >= 2`. Let `S = closedTestPullback(...).Common` be the ACTUAL source separator and `q_S : S -> B` the canonical HJ `A -> B` part map on that root. Construct a strict original-partial old-side extension **relative to the SAME target root**, respecting all prior projected A-copy intersections and all predecessor histories. The current power-core extension and append theorem can then glue it.

Do **not** request the extension for arbitrary pairs of forest stages, arbitrary roots, or arbitrary side maps: C5/marked-parity counterexamples make those predicates false. Do **not** replace `T` or `S` by generated hulls to improve cardinalities. The final theorem must retain positive function arity hypotheses where used, full protected irreducible B-copies, part-transversal output fibres, and the source-defined (not total-fibre) external homomorphism.

A practical next theorem should prove that the true HJ **trace/history of attachments** supplies precisely the missing old-side relative witness on every maximal mixed root, or else produce a counterexample satisfying *all* rank-predecessor and class assumptions. If neither is established, remain explicitly **OPEN**. The existing verified 2019 U-closed/relative completion route does not depend on this optional strengthening.

## Verification gate

CI workflow `.github/workflows/lean.yml` compiles all imports referenced by `Check*.lean` and runs `#print axioms` checks. A failed or pending workflow leaves these new theorem sources as **candidates**. No manuscript TeX has been changed on this track.
