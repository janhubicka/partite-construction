import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Ramsey.ClosureEmbeddingRange
import PartiteConstruction.Iterated.AttachmentProjection
import PartiteConstruction.Iterated.AttachmentDecompose

/-! # Protected tests in the actual simultaneous Picture attachment

This is the existing Attachment.attach construction, not an abstract
free-amalgam witness supplied by a caller. Removing the exterior of one
copy leaves a relative U-substructure whenever the attaching support is
relatively closed in the old picture. A protected closed test therefore
lies in the core or in one attached copy.

Compatible protected maps of the core and copies fold to one protected
map. The target is arbitrary: neither strong amalgamation nor a target
free decomposition is needed for this map theorem. Whole-source closedness
is explicit; the temporary nonclosed recursive Picture is not covered.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}} {V W I X Y : Type v}
variable (Base : RelStructure L V) (S : Set V) (Core : RelStructure L W)
variable (maps : I → Embedding (Base.induce S) Core)

/-- Removing the exterior of one copy preserves relative closure. The
common support's closure condition accounts for tuples rooted in the core. -/
theorem rest_isUSubstructure
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Base S) (i : I) :
    IsUSubstructure rules (attach Base S Core maps)
      {z | ¬ OutsideAt (W := W) (I := I) S i z} := by
  intro rule hrule t ht hRoot j
  rcases ht with ⟨xs, _, heq⟩ | ⟨k, xs, hxs, heq⟩
  · intro hout
    obtain ⟨a, ha⟩ := hout
    have hj : t j = Sum.inl (xs j) := congrFun heq j
    rw [ha] at hj
    cases hj
  · by_cases hki : k = i
    · subst k
      have hInput : ∀ l : Fin rule.rootSize,
          xs (l.castLE rule.rootLE) ∈ S := by
        intro l
        by_contra hNot
        apply hRoot l
        exact ⟨⟨xs (l.castLE rule.rootLE), hNot⟩,
          (congrFun heq (l.castLE rule.rootLE)).trans
            (copyMap_not_mem i (xs (l.castLE rule.rootLE)) hNot)⟩
      have hOut : xs j ∈ S := hS rule hrule xs hxs hInput j
      intro hout
      obtain ⟨a, ha⟩ := hout
      have hj : t j = Sum.inl (maps i ⟨xs j, hOut⟩) :=
        (congrFun heq j).trans (copyMap_mem i (xs j) hOut)
      rw [ha] at hj
      cases hj
    · intro hout
      apply copyMap_not_outside_of_ne
        (B := Base) (S := S) (D := Core) (f := maps) (i := i) k hki (xs j)
      have hj : t j = copyMap Base S Core maps k (xs j) := congrFun heq j
      rw [← hj]
      exact hout

/-- Every embedded protected closed test in a CLOSED Picture attachment
factors through the core or one original copy. No irreducibility of Base,
Core or the attaching support is required. -/
theorem closed_test_core_or_copy
    {rules : ClosureDescription L}
    (hBase : IsUClosed rules Base)
    (hS : IsUSubstructure rules Base S)
    (hWhole : IsUClosed rules (attach Base S Core maps))
    (Test : RelStructure L X) (hTest : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : Embedding Test (attach Base S Core maps)) :
    (∃ g : Embedding Test Core,
      ∀ x, coreEmbedding Base S Core maps (g x) = e x) ∨
    (∃ i : I, ∃ g : Embedding Test Base,
      ∀ x, copyEmbedding Base S Core maps i (g x) = e x) := by
  classical
  by_cases hCore : ∀ x : X, ∃ w : W, e x = Sum.inl w
  · left
    let c := coreEmbedding Base S Core maps
    have hRange (x : X) : ∃ w : W, e x = c w := hCore x
    exact ⟨e.factorThroughRange c hRange,
      fun x => (Classical.choose_spec (hRange x)).symm⟩
  · push Not at hCore
    obtain ⟨a, ha⟩ := hCore
    cases hVal : e a with
    | inl w => exact False.elim (ha w hVal)
    | inr pair =>
      let i : I := pair.1
      let c := copyEmbedding Base S Core maps i
      let LS : Set X := e ⁻¹' Set.range c
      let RS : Set X := {x | ¬ OutsideAt (W := W) (I := I) S i (e x)}
      have hLS : IsUSubstructure rules Test LS :=
        (c.range_isUSubstructure hBase hWhole).preimage_embedding e
      have hRS : IsUSubstructure rules Test RS :=
        (rest_isUSubstructure Base S Core maps hS i).preimage_embedding e
      have hCover (x : X) : x ∈ LS ∨ x ∈ RS := by
        by_cases hx : OutsideAt (W := W) (I := I) S i (e x)
        · left
          obtain ⟨y, hy⟩ := hx
          exact ⟨y.1, (copyMap_not_mem i y.1 y.2).trans hy.symm⟩
        · exact Or.inr hx
      have hTuples : ∀ R (z : Fin (L.arity R) → X), Test.rel R z →
          (∀ k, z k ∈ LS) ∨ (∀ k, z k ∈ RS) := by
        intro R z hz
        have he : (attach Base S Core maps).rel R (e ∘ z) :=
          (e.map_rel_iff R z).mpr hz
        rcases he with ⟨xs, _, heq⟩ | ⟨k, xs, _, heq⟩
        · right
          intro l hout
          obtain ⟨y, hy⟩ := hout
          have hl : e (z l) = Sum.inl (xs l) := congrFun heq l
          rw [hy] at hl
          cases hl
        · by_cases hki : k = i
          · subst k
            left
            intro l
            exact ⟨xs l, (congrFun heq l).symm⟩
          · right
            intro l hout
            apply copyMap_not_outside_of_ne
              (B := Base) (S := S) (D := Core) (f := maps) (i := i)
              k hki (xs l)
            have hl : e (z l) = copyMap Base S Core maps k (xs l) :=
              congrFun heq l
            rw [← hl]
            exact hout
      rcases hIrred.closed_cover hTest LS RS hLS hRS hCover hTuples with
          hAllLeft | hAllRight
      · right
        have hRange (x : X) : ∃ y : V, e x = c y := by
          obtain ⟨y, hy⟩ := hAllLeft x
          exact ⟨y, hy.symm⟩
        exact ⟨i, e.factorThroughRange c hRange,
          fun x => (Classical.choose_spec (hRange x)).symm⟩
      · exact False.elim (hAllRight a ⟨pair.2, hVal⟩)

/-- Compatible core and copy maps fold to a map preserving ALL protected
closed tests of the actual attachment, not only fixed B-copies. -/
theorem fold_isClosedUHomomorphismEmbedding
    {rules : ClosureDescription L}
    (hBase : IsUClosed rules Base)
    (hS : IsUSubstructure rules Base S)
    (hWhole : IsUClosed rules (attach Base S Core maps))
    (Target : RelStructure L Y)
    (pCore : W → Y) (pCopy : I → V → Y)
    (hCore : IsClosedUHomomorphismEmbedding rules Core Target pCore)
    (hCopy : ∀ i, IsClosedUHomomorphismEmbedding rules Base Target (pCopy i))
    (hCompat : ∀ i (x : S), pCore (maps i x) = pCopy i x.1) :
    IsClosedUHomomorphismEmbedding rules (attach Base S Core maps)
      Target (fold pCore pCopy) := by
  let F := fold pCore pCopy
  constructor
  · intro R z hz
    rcases hz with ⟨xs, hxs, heq⟩ | ⟨i, xs, hxs, heq⟩
    · have hTarget : Target.rel R (pCore ∘ xs) := hCore.1 R xs hxs
      convert hTarget using 1
      funext k
      have hk : z k = Sum.inl (xs k) := congrFun heq k
      change F (z k) = pCore (xs k)
      rw [hk]
      rfl
    · have hTarget : Target.rel R (pCopy i ∘ xs) := (hCopy i).1 R xs hxs
      convert hTarget using 1
      funext k
      have hk : z k = copyMap Base S Core maps i (xs k) := congrFun heq k
      change F (z k) = pCopy i (xs k)
      rw [hk]
      exact fold_copy pCore pCopy hCompat i (xs k)
  · intro Z Test hTest hIrred e
    rcases closed_test_core_or_copy Base S Core maps hBase hS hWhole
        Test hTest hIrred e with ⟨g, hg⟩ | ⟨i, g, hg⟩
    · obtain ⟨d, hd⟩ := hCore.on_test Test hTest hIrred g
      refine ⟨d, ?_⟩
      intro x
      calc
        d x = pCore (g x) := hd x
        _ = F (coreEmbedding Base S Core maps (g x)) := rfl
        _ = F (e x) := congrArg F (hg x)
    · obtain ⟨d, hd⟩ := (hCopy i).on_test Test hTest hIrred g
      refine ⟨d, ?_⟩
      intro x
      calc
        d x = pCopy i (g x) := hd x
        _ = F (copyEmbedding Base S Core maps i (g x)) :=
          (fold_copy pCore pCopy hCompat i (g x)).symm
        _ = F (e x) := congrArg F (hg x)

end StructuralRamsey.RelStructure.Attachment
