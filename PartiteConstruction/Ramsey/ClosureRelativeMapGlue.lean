import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Ramsey.ClosureProjectedCompletion

/-! # Closed tests across relatively closed source sides

For the closed-substructure repair, the source of a completion may be a
weak induced test. Neither the source, its two sides, nor their common
cut need be intrinsically U-closed. Relative U-closedness of the two
side ranges suffices: their preimages in a CLOSED irreducible test are
intrinsically closed and freely cover that test.

This removes the closed-common-source-root premise from map gluing and
from the independent projected-completion theorem. The fixed TARGET
boundary Q must still be a closed member of K embedded in both projected
sources. No source boundary is silently replaced by its closure, and no
claim is made that the two projected sources have smaller generating rank.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C X Z : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Relative side ranges localize closed irreducible tests even when
the whole source and the common cut are not intrinsically closed. -/
theorem IsFreeAmalgam.closed_test_factor_of_relative_ranges
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hL : IsUSubstructure rules Whole (Set.range iL))
    (hR : IsUSubstructure rules Whole (Set.range iR))
    (Test : RelStructure L X)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : Embedding Test Whole) :
    (∃ g : Embedding Test Left, ∀ x, iL (g x) = e x) ∨
    (∃ g : Embedding Test Right, ∀ x, iR (g x) = e x) := by
  classical
  let LS : Set X := e ⁻¹' Set.range iL
  let RS : Set X := e ⁻¹' Set.range iR
  have hLS : IsUSubstructure rules Test LS := hL.preimage_embedding e
  have hRS : IsUSubstructure rules Test RS := hR.preimage_embedding e
  have hCover : ∀ x : X, x ∈ LS ∨ x ∈ RS := by
    intro x
    rcases hSrc.covers (e x) with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, ha.symm⟩
    · exact Or.inr ⟨b, hb.symm⟩
  have hTuples : ∀ R (t : Fin (L.arity R) → X), Test.rel R t →
      (∀ k, t k ∈ LS) ∨ (∀ k, t k ∈ RS) := by
    intro R t ht
    rcases (hSrc.rel_iff R (e ∘ t)).mp
        ((e.map_rel_iff R t).mpr ht) with ⟨a, _, ha⟩ | ⟨b, _, hb⟩
    · exact Or.inl (fun k => ⟨a k, (congrFun ha k).symm⟩)
    · exact Or.inr (fun k => ⟨b k, (congrFun hb k).symm⟩)
  rcases hIrred.closed_cover hClosed LS RS hLS hRS hCover hTuples with hAll | hAll
  · have hRange (x : X) : ∃ a : E, e x = iL a := by
      obtain ⟨a, ha⟩ := hAll x
      exact ⟨a, ha.symm⟩
    exact Or.inl ⟨e.factorThroughRange iL hRange,
      fun x => (Classical.choose_spec (hRange x)).symm⟩
  · have hRange (x : X) : ∃ b : F, e x = iR b := by
      obtain ⟨b, hb⟩ := hAll x
      exact ⟨b, hb.symm⟩
    exact Or.inr ⟨e.factorThroughRange iR hRange,
      fun x => (Classical.choose_spec (hRange x)).symm⟩

/-- Relative side data survive restriction to an EXACT weak induced
source. The restricted sides are not asserted intrinsically closed. -/
theorem relative_ranges_on_weak_test
    {rules : ClosureDescription L}
    {Ambient : RelStructure L C} {Test : RelStructure L X}
    (e : Embedding Test Ambient) (S T : Set C)
    (hS : IsUSubstructure rules Ambient S)
    (hT : IsUSubstructure rules Ambient T) :
    IsUSubstructure rules Test (e ⁻¹' S) ∧
      IsUSubstructure rules Test (e ⁻¹' T) :=
  ⟨hS.preimage_embedding e, hT.preimage_embedding e⟩

/-- Compatible maps protecting closed tests glue across relative sides.
The target can add relations; only the SOURCE amalgam must be free. -/
theorem IsClosedUHomomorphismEmbedding.fold_free_of_relative_ranges
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hL : IsUSubstructure rules Whole (Set.range iL))
    (hR : IsUSubstructure rules Whole (Set.range iR))
    {Target : RelStructure L Z}
    (fL : E → Z) (fR : F → Z)
    (hfL : IsClosedUHomomorphismEmbedding rules Left Target fL)
    (hfR : IsClosedUHomomorphismEmbedding rules Right Target fR)
    (hCompat : ∀ d, fL (sL d) = fR (sR d)) :
    IsClosedUHomomorphismEmbedding rules Whole Target
      (hSrc.compatibleFold fL fR hCompat) := by
  let f := hSrc.compatibleFold fL fR hCompat
  constructor
  · intro R t ht
    rcases (hSrc.rel_iff R t).mp ht with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
    · have hMap : f ∘ t = fL ∘ a := by
        funext k
        rw [heq]
        exact hSrc.compatibleFold_left fL fR hCompat (a k)
      change Target.rel R (f ∘ t)
      rw [hMap]
      exact hfL.1 R a ha
    · have hMap : f ∘ t = fR ∘ b := by
        funext k
        rw [heq]
        exact hSrc.compatibleFold_right fL fR hCompat (b k)
      change Target.rel R (f ∘ t)
      rw [hMap]
      exact hfR.1 R b hb
  · intro Y Test hClosed hIrred e
    rcases hSrc.closed_test_factor_of_relative_ranges hL hR
        Test hClosed hIrred e with ⟨a, ha⟩ | ⟨b, hb⟩
    · obtain ⟨j, hj⟩ := hfL.on_test Test hClosed hIrred a
      refine ⟨j, ?_⟩
      intro x
      calc
        j x = fL (a x) := hj x
        _ = f (iL (a x)) :=
          (hSrc.compatibleFold_left fL fR hCompat (a x)).symm
        _ = f (e x) := congrArg f (ha x)
    · obtain ⟨j, hj⟩ := hfR.on_test Test hClosed hIrred b
      refine ⟨j, ?_⟩
      intro x
      calc
        j x = fR (b x) := hj x
        _ = f (iR (b x)) :=
          (hSrc.compatibleFold_right fL fR hCompat (b x)).symm
        _ = f (e x) := congrArg f (hb x)

/-- Independent completions over a fixed CLOSED target boundary glue
also for a nonclosed weak source cut, provided both source sides are
relatively U-closed. No bound on either projected source is assumed. -/
theorem HasClosedUKCompletion.of_independent_projected_completions_relative
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {V : Type v} (D : RelStructure L V), K D → D.Irreducible)
    {P Y : Type v}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hL : IsUSubstructure rules Whole (Set.range iL))
    (hR : IsUSubstructure rules Whole (Set.range iR))
    [Finite P]
    (Q : RelStructure L P) (hQK : K Q) (hQClosed : IsUClosed rules Q)
    (DL : RelStructure L X) (DR : RelStructure L Y)
    (pL : E → X) (pR : F → Y)
    (hpL : IsClosedUHomomorphismEmbedding rules Left DL pL)
    (hpR : IsClosedUHomomorphismEmbedding rules Right DR pR)
    (q : H → P) (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hRootL : ∀ d, pL (sL d) = rL (q d))
    (hRootR : ∀ d, pR (sR d) = rR (q d))
    (hDL : HasClosedUKCompletion K rules DL)
    (hDR : HasClosedUKCompletion K rules DR) :
    HasClosedUKCompletion K rules Whole := by
  obtain ⟨XL, hXL, TL, hTL, _, fL, hfL⟩ := hDL
  obtain ⟨YR, hYR, TR, hTR, _, fR, hfR⟩ := hDR
  letI : Finite XL := hXL
  letI : Finite YR := hYR
  obtain ⟨eL, eR, heL, heR⟩ :=
    IsClosedUHomomorphismEmbedding.common_boundary_embeddings
      hQClosed (hKIrr Q hQK) rL rR hfL hfR
  obtain ⟨Z, hZ, Target, hTarget, jL, jR, hGlue, _⟩ :=
    hK Q TL TR hQK hTL hTR eL eR
  let gL : E → Z := jL ∘ (fL ∘ pL)
  let gR : F → Z := jR ∘ (fR ∘ pR)
  have hgL : IsClosedUHomomorphismEmbedding rules Left Target gL :=
    (jL.isClosedUHomomorphismEmbedding rules).comp (hfL.comp hpL)
  have hgR : IsClosedUHomomorphismEmbedding rules Right Target gR :=
    (jR.isClosedUHomomorphismEmbedding rules).comp (hfR.comp hpR)
  have hCompat : ∀ d, gL (sL d) = gR (sR d) := by
    intro d
    calc
      gL (sL d) = jL (fL (rL (q d))) := congrArg (fun x => jL (fL x)) (hRootL d)
      _ = jL (eL (q d)) := congrArg jL (heL (q d)).symm
      _ = jR (eR (q d)) := hGlue (q d)
      _ = jR (fR (rR (q d))) := congrArg jR (heR (q d))
      _ = gR (sR d) := congrArg (fun x => jR (fR x)) (hRootR d).symm
  exact ⟨Z, hZ, Target, hTarget, hKIrr Target hTarget,
    hSrc.compatibleFold gL gR hCompat,
    IsClosedUHomomorphismEmbedding.fold_free_of_relative_ranges hSrc hL hR
      gL gR hgL hgR hCompat⟩

end StructuralRamsey.RelStructure
