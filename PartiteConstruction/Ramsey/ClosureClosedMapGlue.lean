import PartiteConstruction.Ramsey.ClosureClosedMap
import PartiteConstruction.Ramsey.ClosureRelativeSideRange
import PartiteConstruction.Ramsey.CopywiseFreeFold

/-! # Free gluing of maps preserving closed U-irreducible tests

The source is a free amalgam of U-semi-closed structures over a U-closed
common root. Every embedded U-closed U-irreducible test factors through
one side. We prove this directly on the test's own carrier by pulling
back the two side ranges, with no image-isomorphism assumption.

Compatible positive side maps therefore glue to a positive map preserving
ALL protected closed tests, not just a single fixed B. The target can be
an arbitrary relational structure: no target free-amalgamation assumption
is used. This is the working closed-test convention, not a redefinition
of the literal 2019 U-homomorphism-embedding predicate.
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

/-- Carrier-independent version of closed-test side localization.
The inverse images in Test are relatively closed, hence intrinsically
closed because Test itself is closed. They form a free decomposition. -/
theorem IsFreeAmalgam.closed_test_factor
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (Test : RelStructure L X)
    (hTest : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : Embedding Test Whole) :
    (∃ g : Embedding Test Left, ∀ x, iL (g x) = e x) ∨
    (∃ g : Embedding Test Right, ∀ x, iR (g x) = e x) := by
  classical
  let LS : Set X := e ⁻¹' Set.range iL
  let RS : Set X := e ⁻¹' Set.range iR
  let MS : Set X := LS ∩ RS
  have hLS : IsUClosed rules (Test.induce LS) :=
    hTest.induce_of_USubstructure LS
      ((hSrc.left_range_isUSubstructure hRoot hRight).preimage_embedding e)
  have hRS : IsUClosed rules (Test.induce RS) :=
    hTest.induce_of_USubstructure RS
      ((hSrc.right_range_isUSubstructure hRoot hLeft).preimage_embedding e)
  let mL : Embedding (Test.induce MS) (Test.induce LS) := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : LS => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let mR : Embedding (Test.induce MS) (Test.induce RS) := {
    toFun := fun x => ⟨x.1, x.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : RS => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let l : Embedding (Test.induce LS) Test := inclusion Test LS
  let r : Embedding (Test.induce RS) Test := inclusion Test RS
  have hFree : IsFreeAmalgam mL mR l r := by
    constructor
    · intro x
      rcases hSrc.covers (e x) with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨⟨x, ⟨a, ha.symm⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨x, ⟨b, hb.symm⟩⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have hab0 : a.1 = b.1 := hab
        have haR : a.1 ∈ RS := by rw [hab0]; exact b.2
        let d : MS := ⟨a.1, a.2, haR⟩
        exact ⟨d, Subtype.ext rfl, Subtype.ext hab0.symm⟩
      · rintro ⟨d, rfl, rfl⟩
        rfl
    · intro R t
      constructor
      · intro ht
        have he : Whole.rel R (e ∘ t) := (e.map_rel_iff R t).mpr ht
        rcases (hSrc.rel_iff R (e ∘ t)).mp he with
            ⟨a, _, ha⟩ | ⟨b, _, hb⟩
        · have hArgs : ∀ k, t k ∈ LS := by
            intro k
            exact ⟨a k, (congrFun ha k).symm⟩
          let x : Fin (L.arity R) → LS := fun k => ⟨t k, hArgs k⟩
          exact Or.inl ⟨x, ht, rfl⟩
        · have hArgs : ∀ k, t k ∈ RS := by
            intro k
            exact ⟨b k, (congrFun hb k).symm⟩
          let x : Fin (L.arity R) → RS := fun k => ⟨t k, hArgs k⟩
          exact Or.inr ⟨x, ht, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact hx
        · exact hx
  rcases hIrred hLS hRS hFree with hSurjL | hSurjR
  · have hRange (x : X) : ∃ a : E, e x = iL a := by
      obtain ⟨y, hy⟩ := hSurjL x
      obtain ⟨a, ha⟩ := y.2
      exact ⟨a, (congrArg e hy).symm.trans ha.symm⟩
    left
    exact ⟨e.factorThroughRange iL hRange,
      fun x => (Classical.choose_spec (hRange x)).symm⟩
  · have hRange (x : X) : ∃ b : F, e x = iR b := by
      obtain ⟨y, hy⟩ := hSurjR x
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, (congrArg e hy).symm.trans hb.symm⟩
    right
    exact ⟨e.factorThroughRange iR hRange,
      fun x => (Classical.choose_spec (hRange x)).symm⟩

/-- Compatible side maps glue to a positive map preserving all closed
U-irreducible tests. Only the SOURCE amalgam is free. -/
theorem IsClosedUHomomorphismEmbedding.fold_free
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
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
    rcases hSrc.closed_test_factor hRoot hLeft hRight
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

end StructuralRamsey.RelStructure
