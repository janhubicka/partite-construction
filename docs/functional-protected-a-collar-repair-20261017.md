# Repairing the functional Appendix A iteration: exact protected (A)-collars

**17 October 2026.** English proof proposal and adversarial audit, prior to further Lean formalization. This concerns the actual induced/iterated partite construction in the natural language of set-valued functions, not the alternative `U`-closed/profile relational proof.

## Correct objects and target

Work after the already checked recursive Ramsey theorem, with a genuine functional Ramsey control (D). The iterated construction uses a genuine functional `System`, whose set-valued output fibres remain transversal under the part map. The base (B) is **irreducible** and its embeddings and free-amalgam roots are full/function-closed. The global stage projection is EHN / source-defined original-2019 partial; no domain reflection at source-undefined tuples is assumed.

For every exact finite vertex set (S), the test is `C.weakInduce S`; neither it nor its projected set (p[S]) is replaced by a generated closure. The desired inductive witness is a STRICT genuine full-functional (B)-tree with an **ambient-relative weak HE** of this exact test; on a genuinely closed test it becomes an original-2019 partial HE.

## A protected marked A-copy is the missing relative condition

Fix a control placement (alpha:Ahookrightarrow D), a weak test (Ssubseteq C), a projection (p:C	o D), a target strict (B)-tree (T), a weak completion map (f:S	o T), and a full marked copy (a_T:Ahookrightarrow T) contained in a (B)-constituent. Define the **exact marked trace**

[
  orall sin S;orall ain A:
  quad f(s)=a_T(a)quadLongleftrightarrowquad p(s)=alpha(a).
]

The **reverse implication** (“anchoring”) is provided on a predecessor test by the existing ambient-full-(A)-copy intersection certificate: (D) contains the *whole* (alpha)-copy, even when only a weak piece is tested.

The **forward implication** (“no wrong hit”) is NOT supplied by ordinary projected histories. It is automatic if the target tree admits an EHN part map (t:T	o D) satisfying (t f=p|_S) and (t a_T=alpha). An alternative is to retain only this protected trace, without imposing a global map on all vertices of (T).

## Exact mixed-step argument, given two protected traces

Suppose a tested weak substructure in a genuine FULL functional free attachment (C=L*_R M) has an exact common root (R_S); its part projection lies in (alpha[A]). Choose two strict functional (B)-tree witnesses (T_L,T_M), with full marked (A)-copies (a_L,a_M), such that their respective maps from the exact weak side sets have the protected trace above. Require the previously checked ambient-relative weak HE, preservation of all actually embedded full (A)-copy intersections, and arbitrary projected histories on the sides.

Glue (T_L,T_M) by a **FULL functional free amalgam over (A)**, identifying (a_L(a)) with (a_M(a)) for every (ain A). This is strict because both marked (A)-copies are contained in irreducible (B)-constituents. Root agreement follows by mapping each source-root vertex with projected label (alpha(a)) to the common target vertex labelled (a).

A cross-side collision in the target free amalgam occurs only through a marked (A)-vertex. By the **forward** direction of the protected traces the two source vertices have the same projected label (alpha(a)). Thus arbitrary projected histories survive. The already verified ambient-relative weak-HE and actual ambient-(A)-copy gluing lemmas then give a strict full-functional weak-tree witness of the whole exact test. On a closed test the existing upgrade yields the original-2019 strict completion.

This is a sound **conditional** gluing theorem, suitable for Lean. It is deliberately weaker than requiring a global EHN label map on every target (B)-tree vertex, which is unnecessary for this one gluing step.

## Audited abstract mixed rank-increment lemma

A sharper intermediate theorem isolates the problematic **mixed** case
without any Hales--Jewett-specific proof replay.

Let (C=L *_R M) be a genuine full functional free amalgam, with EHN
part map (p:C\to D), and assume every point of the full attaching
root (R) projects into the image of one actual full control
embedding (alpha:A\hookrightarrow D). Suppose the *previous control*
(D) has an exact protected-(alpha) strict (B)-tree witness for
**every** weak test of at most (n-1) vertices, with every requested
finite projected history. Let (S\subseteq C) have (|S|\le n) and
meet BOTH sides beyond the common root.

Then the exact side tests
(S_L=i_L^{-1}[S]) and (S_M=i_M^{-1}[S]) have strictly fewer
than (n) vertices. Their exact projected images in (D) have
at most (n-1) vertices. Pull back the two protected predecessor
witnesses along the EHN side maps (L\to D), (M\to D).
They share the prescribed (alpha)-mark by construction.
The preceding conditional gluing theorem then gives a strict
functional (B)-tree witness on the whole exact weak (S), with
all ambient (A)-intersection and history certificates.

**Adversarial audit.** This lemma explicitly requires the
predecessor **protected** rank-((n-1)) property on (D), not just
separate rank-(n) tree completability of (L,M).
The arbitrary-stage (C_5) counterexample violates this extra
predecessor premise for its complete control (K_5).
The genuine three-line (C_7) example violates the corresponding
rank-six predecessor premise for (K_3). Thus neither refutes the
statement. No closure of (S) or (p[S]) is invoked.

This proves ONLY the mixed branch. Pure-side inheritance of the
**ambient** (A)-copy history is not entirely formal: an ambient
full (A)-copy from the other side can intersect a pure test through
the attaching root. The complete Picture induction must handle
that history restriction separately, rather than declaring a
whole-stage theorem directly from the abstract mixed lemma.

## The published two-case induction

* If (|p[S]|<n), use the predecessor weak-test witness on the exact projected image. The commuting-parts EHN pullback and ambient histories are already checked.
* If (|p[S]|=n=|S|), the projected part map is injective on the tested vertices. For a genuinely mixed binary attachment both exact weak sides are proper, so their projected sizes are (le n-1). Request **protected marked-(A)** predecessor witnesses on those projected subsets for the actual attaching (alpha); pull them back and glue as above.
* The initial genuine strict (B)-tree and active HJ power have labelled one-copy witnesses. Whole finite families of HJ lines sharing one parameter coordinate also retract to Old and inherit strict weak histories (already proved).
* **Still open:** prove that protected marked-(A) predecessor witnesses can be chosen and retained through *arbitrary* genuine line attachment families, where the parameter sets need not meet. In particular one cannot obtain their “no wrong hit” direction by appealing to existing ordinary histories, a free amalgam over a nonclosed weak root, or a false universal arbitrary-stage maximal-mixed schema.

## Adversarial tests

1. **Wrong-hit example (already for graphs).** Let (A=B=K_2), (D=K_3), (alpha:A	o D) select (0,1), and test (I={0,2}). Map the induced source edge into a single (K_2), with (f(0)=0) and (f(2)=1), and mark the same target edge as the (alpha)-copy. The marked copy *correctly extends* the tested intersection with (alpha); the map is full on the tested edge and obeys all singleton-projected histories because it is injective there. Nevertheless (f(2)=a_T(1)) while (2
ealpha(1)). Thus **anchoring + histories does not imply no-wrong-hit**. A different witness (a two-edge star with a fresh marked edge) can repair this particular example, so it is NOT an impossibility proof for the desired existential collar theorem.
2. **False universal hard-root assertion.** The documented (C_5) construction with arbitrary old/core EHN forests refutes the quantification over *all* stages, even with irreducible (B). It has no rank-((n-1)) projected-history premise for its dense control. Do not use `MaximalMixedHardRootSchemaFromTwo` as an unproved “axiom to discharge.”
3. **Actual multi-line (C_7).** The genuine three-line HJ Picture has a seven-vertex odd cycle, so preserving an (n=7) strict tree property from Old and the core *at the same rank* is false. Its seven tested vertices project to only three control parts; a legitimate rank-seven proof must use the small-image predecessor branch, which the counterexample's control (K_3) cannot supply at rank six. No contradiction with the proposed rank increment.
4. **Multiple line intersections.** Pairwise line overlaps lie in closed roots or full (A)-copies, and generating-part overlap improves this. The **union** of overlaps with two distinct lines need not lie in one (A)-copy. Thus do not identify all previous lines along a single arbitrary abstract root by pairwise geometry alone.
5. **Function semantics.** A global total-fibre homomorphism is false for EHN projections. Preserve defined source fibres and full embedded function-closed roots. The separate `PartialSetStructure` syntax additionally distinguishes `none` from `some ∅`; its basic weak-restriction/embedding lemmas are compiled, but an all-arity iterated EHN theorem for this enriched syntax is **not** yet proved.

## Formalization acceptance and status

First formalize **only the valid conditional mixed-gluing theorem with exact protected traces** (and derive traces from labelled witnesses). Check all named axioms. Do not mark the full functional iterated sparsening as validated. Then tackle the genuinely new **protected-collar existence** lemma for actual HJ stages with finite histories, ideally by a proof constructing fresh labelled (B)-constituent witnesses rather than trying to repair arbitrary unlabelled completions after the fact.

The other crucial prospective step is to prove that the collar-existence invariant is preserved under the HJ `attachList` recursion when different attached lines have disjoint parameter sets. That is presently the mathematical gap, not the gluing, Ramsey arrow, or vertex-cardinality estimates.
