import PartiteConstruction.Functional.ClosedTreeAmalgam
import PartiteConstruction.Structure.FreeAmalgam
import PartiteConstruction.Functional.WeakOperations

/-! # Function-language tree amalgams and the closed-graph bridge

This file formalizes the survey's tree-amalgam notion directly for
relation/function structures.  The copy clause is represented by a surjective
full embedding, and every gluing root is required to have its image contained
in a full irreducible substructure of each side.

The main bridge theorem shows that a function-closed relational tree amalgam
of graph encodings decodes to such a genuine function-language tree amalgam.
The closure requirement is exactly what is missing from the naive graph
transfer ruled out by the functional tree-transfer obstruction.
-/

namespace StructuralRamsey

universe u v

namespace Structure

variable {L : Language.{u}}
variable {U V W X Y : Type v}

/-- The image of an embedding is contained in an embedded irreducible full
substructure of its target.  This is the literal function-language analogue
of the containment clause in the survey's tree-amalgam definition. -/
def Embedding.ContainedInIrreducible
    {A : Structure L U} {B : Structure L V}
    (f : Embedding A B) : Prop :=
  ∃ (X : Type v) (E : Structure L X), E.Irreducible ∧
    ∃ j : Embedding E B, ∀ a : U, ∃ x : X, f a = j x

/-- Tree amalgams in the full relation/function language. -/
inductive TreeAmalgam (Base : Structure L V) :
    (W : Type v) → Structure L W → Prop
  | copy {W : Type v} {T : Structure L W}
      (e : Embedding Base T) (hsurj : Function.Surjective e) :
      TreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : Structure L W₁} {T₂ : Structure L W₂}
      {D : Structure L Z} {T : Structure L W}
      (h₁ : TreeAmalgam Base W₁ T₁)
      (h₂ : TreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (hc₁ : f₁.ContainedInIrreducible)
      (hc₂ : f₂.ContainedInIrreducible)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      TreeAmalgam Base W T

end Structure

namespace RelStructure.IsFreeAmalgam

open Structure

variable {L : Language.{u}}
variable {U V W X : Type v}

/-- A relational free-amalgam diagram of function graphs whose two root maps
are closed decodes to a genuine free amalgam of full relation/function
structures.  Closed roots make both side embeddings closed by
sides_closed_iff, so all four displayed maps decode to full embeddings. -/
theorem toFull
    {D : RelStructure L.graph U}
    {A : RelStructure L.graph V}
    {B : RelStructure L.graph W}
    {C : RelStructure L.graph X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hfree : IsFreeAmalgam fA fB iA iB)
    (hfA : FunctionClosedMap D A fA)
    (hfB : FunctionClosedMap D B fB) :
    let cfA : ClosedEmbedding D A := ⟨fA, hfA⟩
    let cfB : ClosedEmbedding D B := ⟨fB, hfB⟩
    let hi := (hfree.sides_closed_iff).2 ⟨hfA, hfB⟩
    let ciA : ClosedEmbedding A C := ⟨iA, hi.1⟩
    let ciB : ClosedEmbedding B C := ⟨iB, hi.2⟩
    Structure.IsFreeAmalgam
      cfA.toFull cfB.toFull ciA.toFull ciB.toFull := by
  dsimp
  let cfA : ClosedEmbedding D A := ⟨fA, hfA⟩
  let cfB : ClosedEmbedding D B := ⟨fB, hfB⟩
  have hi : FunctionClosedMap A C iA ∧ FunctionClosedMap B C iB :=
    (hfree.sides_closed_iff).2 ⟨hfA, hfB⟩
  let ciA : ClosedEmbedding A C := ⟨iA, hi.1⟩
  let ciB : ClosedEmbedding B C := ⟨iB, hi.2⟩
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    rcases hfree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine Or.inl ⟨a, ?_⟩
      change z = iA a
      exact ha
    · refine Or.inr ⟨b, ?_⟩
      change z = iB b
      exact hb
  · intro a b
    constructor
    · intro h
      apply (hfree.overlap a b).mp
      change iA a = iB b at h
      exact h
    · intro h
      change iA a = iB b
      exact (hfree.overlap a b).mpr h
  · intro R z
    change
      C.rel (.inl R) z ↔
        (∃ x : Fin (L.relArity R) → V,
          A.rel (.inl R) x ∧ z = iA ∘ x) ∨
        (∃ y : Fin (L.relArity R) → W,
          B.rel (.inl R) y ∧ z = iB ∘ y)
    exact hfree.rel_iff (.inl R) z
  · intro F x y
    change
      C.rel (.inr F) (funcTuple x y) ↔
        (∃ a : Fin (L.funcArity F) → V, ∃ b : V,
          A.rel (.inr F) (funcTuple a b) ∧
            x = iA ∘ a ∧ y = iA b) ∨
        (∃ a : Fin (L.funcArity F) → W, ∃ b : W,
          B.rel (.inr F) (funcTuple a b) ∧
            x = iB ∘ a ∧ y = iB b)
    constructor
    · intro h
      rcases (hfree.rel_iff (.inr F) (funcTuple x y)).mp h with
        ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
      · let a : Fin (L.funcArity F) → V := fun k => q k.castSucc
        let b : V := q (Fin.last (L.funcArity F))
        refine Or.inl ⟨a, b, ?_, ?_, ?_⟩
        · have heta : funcTuple a b = q := by
            simpa [a, b] using (funcTuple_eta q)
          rw [heta]
          exact hq
        · funext k
          have hk := congrFun heq k.castSucc
          change x k = (iA.toFun ∘ q) k.castSucc
          exact hk
        · have hk := congrFun heq (Fin.last (L.funcArity F))
          change y = (iA.toFun ∘ q) (Fin.last (L.funcArity F))
          exact hk
      · let a : Fin (L.funcArity F) → W := fun k => q k.castSucc
        let b : W := q (Fin.last (L.funcArity F))
        refine Or.inr ⟨a, b, ?_, ?_, ?_⟩
        · have heta : funcTuple a b = q := by
            simpa [a, b] using (funcTuple_eta q)
          rw [heta]
          exact hq
        · funext k
          have hk := congrFun heq k.castSucc
          change x k = (iB.toFun ∘ q) k.castSucc
          exact hk
        · have hk := congrFun heq (Fin.last (L.funcArity F))
          change y = (iB.toFun ∘ q) (Fin.last (L.funcArity F))
          exact hk
    · rintro (⟨a, b, hb, hx, hy⟩ | ⟨a, b, hb, hx, hy⟩)
      · apply (hfree.rel_iff (.inr F) (funcTuple x y)).mpr
        refine Or.inl ⟨funcTuple a b, hb, ?_⟩
        rw [hx, hy]
        exact (comp_funcTuple (fun z => iA z) a b).symm
      · apply (hfree.rel_iff (.inr F) (funcTuple x y)).mpr
        refine Or.inr ⟨funcTuple a b, hb, ?_⟩
        rw [hx, hy]
        exact (comp_funcTuple (fun z => iB z) a b).symm

end RelStructure.IsFreeAmalgam

namespace RelStructure.FunctionClosedTreeAmalgam

open Structure

variable {L : Language.{u}}
variable {U V W X : Type v}

/-- A function-closed relational tree of graph encodings is a genuine tree
amalgam in the original function language.  Irreducibility of the full base is
used only to witness the survey's containment condition for each gluing root. -/
theorem toFunctional
    {Base : Structure L V}
    {T : RelStructure L.graph W}
    (hBase : Base.Irreducible)
    (hT : FunctionClosedTreeAmalgam Base.graph W T) :
    Structure.TreeAmalgam Base W (Structure.ofGraph T) := by
  induction hT with
  | copy h =>
      let e := Structure.Embedding.ofClosedGraphTarget h.toClosedEmbedding
      refine .copy e ?_
      intro y
      refine ⟨h.toEquiv.symm y, ?_⟩
      exact h.toEquiv.apply_symm_apply y
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hf₁ hf₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      let cf₁ : ClosedEmbedding D T₁ := ⟨f₁, hf₁⟩
      let cf₂ : ClosedEmbedding D T₂ := ⟨f₂, hf₂⟩
      have hsides :
          FunctionClosedMap T₁ T i₁ ∧ FunctionClosedMap T₂ T i₂ :=
        glue_sides_closed hf₁ hf₂ hfree
      let ci₁ : ClosedEmbedding T₁ T := ⟨i₁, hsides.1⟩
      let ci₂ : ClosedEmbedding T₂ T := ⟨i₂, hsides.2⟩
      have hc₁full : cf₁.toFull.ContainedInIrreducible := by
        obtain ⟨j, hj⟩ := h₁.root_contained_in_closed_copy f₁ hc₁
        let jf : Structure.Embedding Base (Structure.ofGraph T₁) :=
          Structure.Embedding.ofClosedGraphTarget j
        refine ⟨V, Base, hBase, jf, ?_⟩
        intro d
        obtain ⟨b, hb⟩ := hj d
        exact ⟨b, hb⟩
      have hc₂full : cf₂.toFull.ContainedInIrreducible := by
        obtain ⟨j, hj⟩ := h₂.root_contained_in_closed_copy f₂ hc₂
        let jf : Structure.Embedding Base (Structure.ofGraph T₂) :=
          Structure.Embedding.ofClosedGraphTarget j
        refine ⟨V, Base, hBase, jf, ?_⟩
        intro d
        obtain ⟨b, hb⟩ := hj d
        exact ⟨b, hb⟩
      have hfull :=
        RelStructure.IsFreeAmalgam.toFull hfree hf₁ hf₂
      exact .glue ih₁ ih₂ cf₁.toFull cf₂.toFull
        hc₁full hc₂full ci₁.toFull ci₂.toFull hfull

end RelStructure.FunctionClosedTreeAmalgam
end StructuralRamsey
