import PartiteConstruction.Iterated.LocalTreeLike

/-! # Weak vertex-exact restriction of a relational free amalgam

The free-amalgam geometry restricts to every induced vertex subset, with
no closure assumption on that subset.  Each new side and common root is
the inverse image of the SAME vertex set, and the restricted whole is
the ordinary relational induced structure on exactly those vertices.

This is the relational/graph-encoding interface for weak tests in the
iterated Picture induction, and is logically separate from requiring
the restricted sides to be U-closed.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Every arbitrary *weak* induced subset of a relational free amalgam
is a free amalgam of the induced inverse images.  In particular no
closure hull of the subset or of either projected image is taken. -/
theorem IsFreeAmalgam.weakInduce_withMaps
    (hFree : IsFreeAmalgam sL sR iL iR)
    (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    ∃ (mL : Embedding (Root.induce Mset) (Left.induce Lset))
      (mR : Embedding (Root.induce Mset) (Right.induce Rset))
      (jL : Embedding (Left.induce Lset) (Whole.induce S))
      (jR : Embedding (Right.induce Rset) (Whole.induce S)),
      IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL a).1 = iL a.1) ∧
      (∀ b : Rset, (jR b).1 = iR b.1) := by
  classical
  dsimp only
  let Lset : Set E := iL ⁻¹' S
  let Rset : Set F := iR ⁻¹' S
  let Mset : Set H := (iL.comp sL) ⁻¹' S
  let LS := Left.induce Lset
  let RS := Right.induce Rset
  let MS := Root.induce Mset
  let WS := Whole.induce S

  let mL : Embedding MS LS := {
    toFun := fun x => ⟨sL x.1, x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply sL.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change Left.rel R (sL ∘ (Subtype.val ∘ x)) ↔
        Root.rel R (Subtype.val ∘ x)
      exact sL.map_rel_iff R (Subtype.val ∘ x)
  }
  let mR : Embedding MS RS := {
    toFun := fun x => ⟨sR x.1, by
      change iR (sR x.1) ∈ S
      have hglue : iL (sL x.1) = iR (sR x.1) :=
        (hFree.overlap (sL x.1) (sR x.1)).mpr
          ⟨x.1, rfl, rfl⟩
      rw [← hglue]
      exact x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply sR.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change Right.rel R (sR ∘ (Subtype.val ∘ x)) ↔
        Root.rel R (Subtype.val ∘ x)
      exact sR.map_rel_iff R (Subtype.val ∘ x)
  }
  let jL : Embedding LS WS := {
    toFun := fun x => ⟨iL x.1, x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply iL.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change Whole.rel R (iL ∘ (Subtype.val ∘ x)) ↔
        Left.rel R (Subtype.val ∘ x)
      exact iL.map_rel_iff R (Subtype.val ∘ x)
  }
  let jR : Embedding RS WS := {
    toFun := fun x => ⟨iR x.1, x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply iR.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change Whole.rel R (iR ∘ (Subtype.val ∘ x)) ↔
        Right.rel R (Subtype.val ∘ x)
      exact iR.map_rel_iff R (Subtype.val ∘ x)
  }
  refine ⟨mL, mR, jL, jR, ?_, ?_, ?_⟩
  · constructor
    · intro z
      rcases hFree.covers z.1 with ⟨a, ha⟩ | ⟨b, hb⟩
      · have haS : a ∈ Lset := by
          change iL a ∈ S
          rw [← ha]
          exact z.2
        exact Or.inl ⟨⟨a, haS⟩, by
          apply Subtype.ext
          exact ha⟩
      · have hbS : b ∈ Rset := by
          change iR b ∈ S
          rw [← hb]
          exact z.2
        exact Or.inr ⟨⟨b, hbS⟩, by
          apply Subtype.ext
          exact hb⟩
    · intro a b
      constructor
      · intro hab
        have habWhole : iL a.1 = iR b.1 :=
          congrArg Subtype.val hab
        obtain ⟨d, had, hbd⟩ :=
          (hFree.overlap a.1 b.1).mp habWhole
        have hdS : iL (sL d) ∈ S := by
          rw [← had]
          exact a.2
        let dS : Mset := ⟨d, hdS⟩
        refine ⟨dS, ?_, ?_⟩
        · apply Subtype.ext
          exact had
        · apply Subtype.ext
          exact hbd
      · rintro ⟨d, rfl, rfl⟩
        apply Subtype.ext
        exact (hFree.overlap (sL d.1) (sR d.1)).mpr
          ⟨d.1, rfl, rfl⟩
    · intro R z
      constructor
      · intro hz
        have hzWhole : Whole.rel R (Subtype.val ∘ z) := hz
        rcases (hFree.rel_iff R (Subtype.val ∘ z)).mp hzWhole with
            ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · have hxS : ∀ k : Fin (L.arity R), x k ∈ Lset := by
            intro k
            change iL (x k) ∈ S
            have hk : (z k).1 = iL (x k) := congrFun heq k
            rw [← hk]
            exact (z k).2
          let xs : Fin (L.arity R) → Lset :=
            fun k => ⟨x k, hxS k⟩
          refine Or.inl ⟨xs, ?_, ?_⟩
          · exact hx
          · funext k
            apply Subtype.ext
            exact congrFun heq k
        · have hxS : ∀ k : Fin (L.arity R), x k ∈ Rset := by
            intro k
            change iR (x k) ∈ S
            have hk : (z k).1 = iR (x k) := congrFun heq k
            rw [← hk]
            exact (z k).2
          let xs : Fin (L.arity R) → Rset :=
            fun k => ⟨x k, hxS k⟩
          refine Or.inr ⟨xs, ?_, ?_⟩
          · exact hx
          · funext k
            apply Subtype.ext
            exact congrFun heq k
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact (jL.map_rel_iff R x).mpr hx
        · exact (jR.map_rel_iff R x).mpr hx

  · intro a
    rfl
  · intro b
    rfl

/-- Compatibility statement forgetting the pointwise equations for the
canonical side maps.  Use `weakInduce_withMaps` when those coordinates
are needed for subsequent U-irreducible localization. -/
theorem IsFreeAmalgam.weakInduce
    (hFree : IsFreeAmalgam sL sR iL iR)
    (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    ∃ (mL : Embedding (Root.induce Mset) (Left.induce Lset))
      (mR : Embedding (Root.induce Mset) (Right.induce Rset))
      (jL : Embedding (Left.induce Lset) (Whole.induce S))
      (jR : Embedding (Right.induce Rset) (Whole.induce S)),
      IsFreeAmalgam mL mR jL jR := by
  obtain ⟨mL, mR, jL, jR, hRestricted, _, _⟩ :=
    hFree.weakInduce_withMaps S
  exact ⟨mL, mR, jL, jR, hRestricted⟩

end StructuralRamsey.RelStructure
