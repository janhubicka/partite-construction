import PartiteConstruction.Functional.SingletonReduction
import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Structure.IrreducibleHomImage

/-! # Forgetting singleton ranks in functional tree constructions

The finite ranked expansion replaces each set-valued function by finitely many
singleton-valued rank functions.  This file records the structural descent
needed after proving sparsening in the ranked language: full embeddings and
free amalgams survive rank reduct, and irreducible pieces of a full functional
tree lie in constituent base copies.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- Forget rank labels on an arbitrary full embedding between ranked
structures.  No coverage hypothesis is needed because both source and target
fibres are reduced by the same union over ranks. -/
def Embedding.rankReduct
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U}
    {B : Structure (L.rankFunctions n) V}
    (e : Embedding A B) :
    Embedding (Structure.rankReduct A) (Structure.rankReduct B) where
  toFun := e
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, ⟨i, hz⟩, rfl⟩
      refine ⟨i, ?_⟩
      have h :
          e z ∈ imageSet e (A.func (F, i) x) :=
        ⟨z, hz, rfl⟩
      rw [e.map_func (F, i) x] at h
      exact h
    · rintro ⟨i, hy⟩
      have h :
          y ∈ imageSet e (A.func (F, i) x) := by
        rw [e.map_func (F, i) x]
        exact hy
      rcases h with ⟨z, hz, rfl⟩
      exact ⟨z, ⟨i, hz⟩, rfl⟩

@[simp] theorem Embedding.rankReduct_apply
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U}
    {B : Structure (L.rankFunctions n) V}
    (e : Embedding A B) (x : U) :
    e.rankReduct x = e x := rfl

/-- Rank reduct preserves concrete full free-amalgam diagrams. -/
theorem IsFreeAmalgam.rankReduct
    {n : ℕ}
    {D : Structure (L.rankFunctions n) U}
    {A : Structure (L.rankFunctions n) V}
    {B : Structure (L.rankFunctions n) W}
    {C : Structure (L.rankFunctions n) X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (h : IsFreeAmalgam fA fB iA iB) :
    IsFreeAmalgam
      fA.rankReduct fB.rankReduct
      iA.rankReduct iB.rankReduct where
  covers := h.covers
  overlap := h.overlap
  rel_iff := h.rel_iff
  func_iff := by
    intro F x y
    constructor
    · rintro ⟨i, hy⟩
      rcases (h.func_iff (F, i) x y).mp hy with hleft | hright
      · rcases hleft with ⟨a, b, hb, hxa, hyb⟩
        exact Or.inl ⟨a, b, ⟨i, hb⟩, hxa, hyb⟩
      · rcases hright with ⟨a, b, hb, hxa, hyb⟩
        exact Or.inr ⟨a, b, ⟨i, hb⟩, hxa, hyb⟩
    · rintro (⟨a, b, ⟨i, hb⟩, hxa, hyb⟩ |
        ⟨a, b, ⟨i, hb⟩, hxa, hyb⟩)
      · exact ⟨i, (h.func_iff (F, i) x y).mpr
          (Or.inl ⟨a, b, hb, hxa, hyb⟩)⟩
      · exact ⟨i, (h.func_iff (F, i) x y).mpr
          (Or.inr ⟨a, b, hb, hxa, hyb⟩)⟩

namespace TreeAmalgam

/-- Every embedded irreducible full structure in a functional tree amalgam is
contained in one of the constituent copies of the base. -/
theorem irreducible_contained_in_copy
    {Base : Structure L V} {T : Structure L W}
    (hT : TreeAmalgam Base W T)
    {A : Structure L U} (hA : A.Irreducible)
    (e : Embedding A T) :
    ∃ j : Embedding Base T,
      ∀ a : U, ∃ b : V, e a = j b := by
  induction hT with
  | copy j hsurj =>
      refine ⟨j, ?_⟩
      intro a
      obtain ⟨b, hb⟩ := hsurj (e a)
      exact ⟨b, hb.symm⟩
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      rcases hA hfree e with hleft | hright
      · let e₁ : Embedding A T₁ :=
          e.factorThroughRange i₁ hleft
        obtain ⟨j₁, hj₁⟩ := ih₁ e₁
        refine ⟨i₁.comp j₁, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₁ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (hleft a)
        change e a = i₁ (j₁ b)
        calc
          e a = i₁ (e₁ a) := by
            simpa [e₁, Embedding.factorThroughRange] using hea
          _ = i₁ (j₁ b) := congrArg i₁ hb
      · let e₂ : Embedding A T₂ :=
          e.factorThroughRange i₂ hright
        obtain ⟨j₂, hj₂⟩ := ih₂ e₂
        refine ⟨i₂.comp j₂, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₂ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (hright a)
        change e a = i₂ (j₂ b)
        calc
          e a = i₂ (e₂ a) := by
            simpa [e₂, Embedding.factorThroughRange] using hea
          _ = i₂ (j₂ b) := congrArg i₂ hb



/-- Forgetting ranks preserves a functional tree amalgam as soon as the
reduced base is irreducible.  Root-containment after reduct is witnessed by
a constituent base copy rather than by reducing an arbitrary intermediate
irreducible witness. -/
theorem rankReduct
    {n : ℕ}
    {Base : Structure (L.rankFunctions n) V}
    {T : Structure (L.rankFunctions n) W}
    (hBaseRed : (Structure.rankReduct Base).Irreducible)
    (hT : TreeAmalgam Base W T) :
    TreeAmalgam (Structure.rankReduct Base) W
      (Structure.rankReduct T) := by
  induction hT with
  | copy e hsurj =>
      exact TreeAmalgam.copy e.rankReduct hsurj
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      have hc₁red :
          (f₁.rankReduct).ContainedInIrreducible := by
        rcases hc₁ with ⟨Q, E, hE, j, hj⟩
        obtain ⟨k, hk⟩ := h₁.irreducible_contained_in_copy hE j
        refine ⟨V, Structure.rankReduct Base, hBaseRed,
          k.rankReduct, ?_⟩
        intro d
        obtain ⟨x, hdx⟩ := hj d
        obtain ⟨b, hxb⟩ := hk x
        exact ⟨b, hdx.trans hxb⟩
      have hc₂red :
          (f₂.rankReduct).ContainedInIrreducible := by
        rcases hc₂ with ⟨Q, E, hE, j, hj⟩
        obtain ⟨k, hk⟩ := h₂.irreducible_contained_in_copy hE j
        refine ⟨V, Structure.rankReduct Base, hBaseRed,
          k.rankReduct, ?_⟩
        intro d
        obtain ⟨x, hdx⟩ := hj d
        obtain ⟨b, hxb⟩ := hk x
        exact ⟨b, hdx.trans hxb⟩
      exact TreeAmalgam.glue
        ih₁ ih₂ f₁.rankReduct f₂.rankReduct
        hc₁red hc₂red i₁.rankReduct i₂.rankReduct
        hfree.rankReduct


/-- A tree may be rebased along a surjective full embedding of base
structures. -/
theorem rebase_surjective
    {Base₀ : Structure L U} {Base₁ : Structure L V}
    {T : Structure L W}
    (hT : TreeAmalgam Base₁ W T)
    (e : Embedding Base₀ Base₁)
    (he : Function.Surjective e) :
    TreeAmalgam Base₀ W T := by
  induction hT with
  | copy j hj =>
      refine TreeAmalgam.copy (j.comp e) ?_
      intro y
      obtain ⟨b, hb⟩ := hj y
      obtain ⟨a, ha⟩ := he b
      refine ⟨a, ?_⟩
      change j (e a) = y
      rw [ha, hb]
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact TreeAmalgam.glue
        ih₁ ih₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree

/-- The canonical ranked expansion reduces back to the original structure by
the identity map whenever all original fibres are covered by the available
ranks. -/
noncomputable def rankExpandReductEmbedding
    (A : Structure L U) [LinearOrder U] [Finite U]
    (n : ℕ) (hA : RankCovered A n) :
    Embedding A
      (Structure.rankReduct (Structure.rankExpand A n)) :=
  (Embedding.id (Structure.rankExpand A n)).forgetRanks hA

theorem rankExpandReductEmbedding_surjective
    (A : Structure L U) [LinearOrder U] [Finite U]
    (n : ℕ) (hA : RankCovered A n) :
    Function.Surjective (rankExpandReductEmbedding A n hA) := by
  intro x
  exact ⟨x, rfl⟩

/-- Final structural singleton-rank descent for tree amalgams. -/
theorem rankExpand_treeReduct
    (Base : Structure L V) [LinearOrder V] [Finite V]
    (n : ℕ) (hCover : RankCovered Base n)
    (hBase : Base.Irreducible)
    {T : Structure (L.rankFunctions n) W}
    (hT : TreeAmalgam (Structure.rankExpand Base n) W T) :
    TreeAmalgam Base W (Structure.rankReduct T) := by
  let e : Embedding Base
      (Structure.rankReduct (Structure.rankExpand Base n)) :=
    rankExpandReductEmbedding Base n hCover
  have he : Function.Surjective e :=
    rankExpandReductEmbedding_surjective Base n hCover
  have hBaseRed :
      (Structure.rankReduct (Structure.rankExpand Base n)).Irreducible :=
    hBase.of_surjective_homomorphism e.isHomomorphism he
  have hRed :
      TreeAmalgam
        (Structure.rankReduct (Structure.rankExpand Base n))
        W (Structure.rankReduct T) :=
    TreeAmalgam.rankReduct hBaseRed hT
  exact hRed.rebase_surjective e he
end TreeAmalgam

end StructuralRamsey.Structure
