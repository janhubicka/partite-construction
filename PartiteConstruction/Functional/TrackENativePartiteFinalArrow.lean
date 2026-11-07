import PartiteConstruction.Functional.TrackECoveredNativeDecoderNoDefinedEmpty2019
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Appendix A Track E: exact native PART-PRESERVING Ramsey endpoint

The corrected two-pass 2019 functional sparse witness gives a genuine
part-preserving Option(Set) Ramsey arrow. Previously audited native arrows
were unpartite, so they cannot simply consume that result: isolated vertex
part labels must be preserved on EVERY A/B full embedding.

We define the native full part-preserving embedding category on the SAME
carrier and transport it through the already verified
`Structure.Embedding.toNonemptyPartial` equivalence. Naturality with
composition yields an EXACT full partite Ramsey-arrow iff, with no
extra witness, closure hull, colour, or rank.

The final decoder theorem directly uses the U-closed / closed
U-irreducible B-copy coverage of the actual tagged 2019 target and the
normality theorem from merged Track E #564. No arbitrary relational
Picture is assumed to be a native function structure in advance.
-/

namespace StructuralRamsey.Structure.TrackENativePartiteFinalArrow

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {VA VB VC : Type v}

/-- Native full embedding preserving every actual vertex part, including
isolated vertices. This is a subtype of full FUNCTIONAL embeddings, not
an EHN homomorphism-embedding or a relational-graph embedding. -/
abbrev NativePartPreservingEmbedding
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts) :=
  {e : Structure.Embedding A B //
    ∀ x, partB (e x) = partA x}

namespace NativePartPreservingEmbedding

/-- Composition keeps the identical vertex maps and full function fibres. -/
def comp
    {A : Structure L VA} {B : Structure L VB} {C : Structure L VC}
    {partA : VA → Parts} {partB : VB → Parts} {partC : VC → Parts}
    (g : NativePartPreservingEmbedding B partB C partC)
    (f : NativePartPreservingEmbedding A partA B partB) :
    NativePartPreservingEmbedding A partA C partC :=
  ⟨g.1.comp f.1, by
    intro x
    change partC (g.1 (f.1 x)) = partA x
    rw [g.2 (f.1 x), f.2 x]⟩

end NativePartPreservingEmbedding

/-- Full native part-labelled embeddings and TRUE independent-domain
part-labelled embeddings are exactly equivalent on the SAME vertex
functions. The existing full-embedding equivalence supplies BOTH
directions; no domain reflection is imposed on any global EHN map. -/
noncomputable def nativePartPreservingEmbeddingEquiv
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts) :
    NativePartPreservingEmbedding A partA B partB ≃
      PartialSetStructure.PartPreservingEmbedding
        A.toNonemptyPartial partA B.toNonemptyPartial partB where
  toFun e := ⟨e.1.toNonemptyPartial, e.2⟩
  invFun e := ⟨partialFullEmbedding_toNative e.1, e.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Structure.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    apply PartialSetStructure.Embedding.ext
    intro x
    rfl

/-- Genuine native set-valued-function partite Ramsey arrow.
Colourings range over FULL part-preserving native A-copies, with a
monochromatic FULL part-preserving native B-copy. -/
def NativePartPreservingArrow
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts)
    (C : Structure L VC) (partC : VC → Parts)
    (κ : Type*) : Prop :=
  ∀ χ : NativePartPreservingEmbedding A partA C partC → κ,
    ∃ b : NativePartPreservingEmbedding B partB C partC,
      ∀ a₁ a₂ : NativePartPreservingEmbedding A partA B partB,
        χ (b.comp a₁) = χ (b.comp a₂)

/-- A full native composite maps to the exact same full genuine-partial
composite. This naturality is essential for transferring monochromatic
B-copies, not just comparing the number of A-copies. -/
theorem nativePartPreservingEmbedding_map_comp
    {A : Structure L VA} {B : Structure L VB} {C : Structure L VC}
    {partA : VA → Parts} {partB : VB → Parts} {partC : VC → Parts}
    (b : NativePartPreservingEmbedding B partB C partC)
    (a : NativePartPreservingEmbedding A partA B partB) :
    nativePartPreservingEmbeddingEquiv A partA C partC (b.comp a) =
      (nativePartPreservingEmbeddingEquiv B partB C partC b).comp
        (nativePartPreservingEmbeddingEquiv A partA B partB a) := by
  apply Subtype.ext
  apply PartialSetStructure.Embedding.ext
  intro x
  rfl

/-- EXACT iff of native and genuine partial part-preserving Ramsey
arrows, with identical A/B/C carriers and part maps. All source and
target function symbol arities are retained (including nullaries).
No hereditary or transversality hypotheses are needed for this
embedding-level logical equivalence. -/
theorem nativePartPreservingArrow_iff_partial
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts)
    (C : Structure L VC) (partC : VC → Parts)
    (κ : Type*) :
    NativePartPreservingArrow A partA B partB C partC κ ↔
      PartialSetStructure.PartPreservingArrow
        A.toNonemptyPartial partA B.toNonemptyPartial partB
        C.toNonemptyPartial partC κ := by
  let ΦAB := nativePartPreservingEmbeddingEquiv A partA B partB
  let ΦBC := nativePartPreservingEmbeddingEquiv B partB C partC
  let ΦAC := nativePartPreservingEmbeddingEquiv A partA C partC
  have hNat
      (b : NativePartPreservingEmbedding B partB C partC)
      (a : NativePartPreservingEmbedding A partA B partB) :
      ΦAC (b.comp a) = (ΦBC b).comp (ΦAB a) :=
    nativePartPreservingEmbedding_map_comp b a
  constructor
  · intro hArrow χ
    obtain ⟨b, hb⟩ := hArrow (fun a => χ (ΦAC a))
    refine ⟨ΦBC b, ?_⟩
    intro a₁ a₂
    let a₁' : NativePartPreservingEmbedding A partA B partB := ΦAB.symm a₁
    let a₂' : NativePartPreservingEmbedding A partA B partB := ΦAB.symm a₂
    have ha₁ : ΦAB a₁' = a₁ := ΦAB.apply_symm_apply a₁
    have ha₂ : ΦAB a₂' = a₂ := ΦAB.apply_symm_apply a₂
    have hn₁ : ΦAC (b.comp a₁') = (ΦBC b).comp a₁ := by
      rw [← ha₁]
      exact hNat b a₁'
    have hn₂ : ΦAC (b.comp a₂') = (ΦBC b).comp a₂ := by
      rw [← ha₂]
      exact hNat b a₂'
    rw [← hn₁, ← hn₂]
    exact hb a₁' a₂'
  · intro hArrow χ
    obtain ⟨b, hb⟩ := hArrow (fun a => χ (ΦAC.symm a))
    let g : NativePartPreservingEmbedding B partB C partC := ΦBC.symm b
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hg : ΦBC g = b := ΦBC.apply_symm_apply b
    have hNat' (a : NativePartPreservingEmbedding A partA B partB) :
        ΦAC (g.comp a) = b.comp (ΦAB a) := by
      rw [← hg]
      exact hNat g a
    have hReflect (a : NativePartPreservingEmbedding A partA B partB) :
        ΦAC.symm (b.comp (ΦAB a)) = g.comp a := by
      apply ΦAC.injective
      simpa only [ΦAC.apply_symm_apply] using (hNat' a).symm
    calc
      χ (g.comp a₁) =
          χ (ΦAC.symm (b.comp (ΦAB a₁))) := by
            exact congrArg χ (hReflect a₁).symm
      _ = χ (ΦAC.symm (b.comp (ΦAB a₂))) :=
            hb (ΦAB a₁) (ΦAB a₂)
      _ = χ (g.comp a₂) :=
            congrArg χ (hReflect a₂)

/-- For any genuinely partial final target P with no defined-empty
operations, the TRUE native full part-preserving arrow after collapsing
the independent domain bit is exactly the original true partial
part-preserving arrow on the SAME P and actual part map. -/
theorem nativePartPreservingArrow_iff_partialTarget_of_noDefinedEmpty
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts)
    (D : PartialSetStructure L VC) (partD : VC → Parts)
    (κ : Type*)
    (hNormal : NoDefinedEmptyValues D) :
    NativePartPreservingArrow A partA B partB
      D.collapseDomain partD κ ↔
      PartialSetStructure.PartPreservingArrow
        A.toNonemptyPartial partA B.toNonemptyPartial partB
        D partD κ := by
  have hEq : D.collapseDomain.toNonemptyPartial = D :=
    (noDefinedEmpty_iff_nativeRoundtrip D).mp hNormal
  have hCanonical :
      NativePartPreservingArrow A partA B partB
        D.collapseDomain partD κ ↔
      PartialSetStructure.PartPreservingArrow
        A.toNonemptyPartial partA B.toNonemptyPartial partB
        D.collapseDomain.toNonemptyPartial partD κ :=
    nativePartPreservingArrow_iff_partial
      A partA B partB D.collapseDomain partD κ
  simpa only [hEq] using hCanonical

/-- FINAL native arrow decoder: exact old U-closedness and canonical
B-cover imply decoder normality, so no independent normality hypothesis
is needed. The part map is precisely the one recovered from unary part
predicates in the ACTUAL tagged C, and every A/B copy keeps its
original part label and function-value set.

This is the endgame semantic transfer on a supplied actual 2019 final
covered target C, not the existence of such a C or a new strict
full-functional mixed-root sparsening theorem. -/
theorem nativePartPreservingArrow_iff_coveredOriginalDecode
    (A : Structure L VA) (partA : VA → Parts)
    (B : Structure L VB) (partB : VB → Parts)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VC)
    (hClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          (((B.toNonemptyPartial).withParts partB).wholeMaskPatternGraph partB))))
    (κ : Type*) :
    NativePartPreservingArrow A partA B partB
      (wholeMaskOriginalDecode C).collapseDomain
      (wholeMaskCoveredPart C B.toNonemptyPartial partB hClosed hCover) κ ↔
      PartialSetStructure.PartPreservingArrow
        A.toNonemptyPartial partA B.toNonemptyPartial partB
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B.toNonemptyPartial partB hClosed hCover) κ := by
  exact nativePartPreservingArrow_iff_partialTarget_of_noDefinedEmpty
    A partA B partB
    (wholeMaskOriginalDecode C)
    (wholeMaskCoveredPart C B.toNonemptyPartial partB hClosed hCover)
    κ
    (wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
      C B partB hClosed hCover)

end StructuralRamsey.Structure.TrackENativePartiteFinalArrow
