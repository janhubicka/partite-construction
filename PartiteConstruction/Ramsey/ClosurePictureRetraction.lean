import PartiteConstruction.Ramsey.ClosureAttachmentFold
import PartiteConstruction.Ramsey.ClosureProjectedGenerators

/-! # Return to the old picture instead of paying for a boundary

A common core retraction that inverts the selected attaching embeddings
extends to a protected map of the ACTUAL attachment back to the old
picture, acting as the identity in every attached old copy. The previous
old-picture rank invariant then completes any rank-bounded test mapping
into this attachment. No absolute rank drop on the two sides is needed.

This handles a precise history branch. A common retraction is not asserted
for all Hales--Jewett lines: a coordinate may be variable on some lines
and constant on others. The remaining proof must either select a compatible
subfamily supporting the test or treat the other branch separately.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}} {V W I X : Type v}
variable (Old : RelStructure L V) (S : Set V) (Core : RelStructure L W)
variable (maps : I → Embedding (Old.induce S) Core)

/-- A common left inverse on the attaching support extends to a protected
map back to the old picture. The conclusion records identity on EVERY
attached old copy, not merely on its support. -/
theorem protected_retraction_to_old
    {rules : ClosureDescription L}
    (hOld : IsUClosed rules Old) (hS : IsUSubstructure rules Old S)
    (hWhole : IsUClosed rules (attach Old S Core maps))
    (r : W → V) (hr : IsClosedUHomomorphismEmbedding rules Core Old r)
    (hInverse : ∀ i (x : S), r (maps i x) = x.1) :
    ∃ p : Vertex S (W := W) (I := I) → V,
      IsClosedUHomomorphismEmbedding rules (attach Old S Core maps) Old p ∧
      (∀ w, p (coreEmbedding Old S Core maps w) = r w) ∧
      (∀ i x, p (copyEmbedding Old S Core maps i x) = x) := by
  let pCopy : I → V → V := fun _ x => x
  have hCopy : ∀ i, IsClosedUHomomorphismEmbedding rules Old Old (pCopy i) :=
    fun _ => (Embedding.id Old).isClosedUHomomorphismEmbedding rules
  refine ⟨fold r pCopy, ?_, ?_, ?_⟩
  · exact fold_isClosedUHomomorphismEmbedding Old S Core maps
      hOld hS hWhole Old r pCopy hr hCopy hInverse
  · intro w
    rfl
  · intro i x
    exact fold_copy r pCopy hInverse i x

/-- A rank-n old-picture invariant remains usable on a tested source
that maps through such a retracted attachment. The tested source can be
nonclosed; only its chosen generating set is counted. -/
theorem completion_from_old_rank_via_retraction
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old) (hS : IsUSubstructure rules Old S)
    (hWhole : IsUClosed rules (attach Old S Core maps))
    (r : W → V) (hr : IsClosedUHomomorphismEmbedding rules Core Old r)
    (hInverse : ∀ i (x : S), r (maps i x) = x.1)
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.induce T) → USize rules (Old.induce T) ≤ n →
        HasClosedUKCompletion K rules (Old.induce T))
    (Test : RelStructure L X)
    (e : Embedding Test (attach Old S Core maps))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n) :
    HasClosedUKCompletion K rules Test := by
  obtain ⟨p, hp, _, _⟩ := protected_retraction_to_old Old S Core maps
    hOld hS hWhole r hr hInverse
  apply HasClosedUKCompletion.of_projected_generators
    hOld (hp.precomp_embedding e) G hGen n hRank
  exact (Finset.card_image_le).trans hSize

/-- A protected retraction also carries the old protected-copy coverage
forward. In particular it preserves the rank-one starting invariant. -/
theorem protected_coverage_of_retraction
    {rules : ClosureDescription L}
    (hOld : IsUClosed rules Old) (hS : IsUSubstructure rules Old S)
    (hWhole : IsUClosed rules (attach Old S Core maps))
    (r : W → V) (hr : IsClosedUHomomorphismEmbedding rules Core Old r)
    (hInverse : ∀ i (x : S), r (maps i x) = x.1)
    {Y : Type v} (Base : RelStructure L Y)
    (hCoverage : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Old → Nonempty (Embedding Test Base)) :
    ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test (attach Old S Core maps) → Nonempty (Embedding Test Base) := by
  obtain ⟨p, hp, _, _⟩ := protected_retraction_to_old Old S Core maps
    hOld hS hWhole r hr hInverse
  intro Z Test hClosed hIrred e
  obtain ⟨d, _⟩ := hp.on_test Test hClosed hIrred e
  exact hCoverage Test hClosed hIrred d

end StructuralRamsey.RelStructure.Attachment
