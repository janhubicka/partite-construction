import PartiteConstruction.Functional.Basic

/-! # Restriction and relabelling for functional partite systems -/
namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} {V : Type w} {Q : Type z}

namespace System

def induce (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S) : System L P S where
  toStructure := B.toStructure.induce S hS
  part x := B.part x.1
  relTransversal R x hx i j hp := by
    apply Subtype.ext
    exact B.relTransversal R (Subtype.val ∘ x) hx i j hp
  funcTransversal F x y z hy hz hp := by
    apply Subtype.ext
    exact B.funcTransversal F (Subtype.val ∘ x) y.1 z.1 hy hz hp

def relabel (B : System L P V) (α : P ↪ Q) : System L Q V where
  toStructure := B.toStructure
  part x := α (B.part x)
  relTransversal R x hx i j hp :=
    B.relTransversal R x hx i j (α.injective hp)
  funcTransversal F x y z hy hz hp :=
    B.funcTransversal F x y z hy hz (α.injective hp)

def support (B : System L P V) (α : Q ↪ P) : Set V :=
  {x | B.part x ∈ Set.range α}

noncomputable def restrictedPart (B : System L P V) (α : Q ↪ P)
    (x : B.support α) : Q :=
  Classical.choose x.property

@[simp] theorem restrictedPart_spec (B : System L P V) (α : Q ↪ P)
    (x : B.support α) :
    α (B.restrictedPart α x) = B.part x.1 :=
  Classical.choose_spec x.property

/-- The selected union of parts is closed under all function symbols whenever
the partition projection is a full homomorphism and the selected parts are the
image of a full substructure embedding. -/
theorem support_closed
    (B : System L P V) (D : Structure L P)
    (hB : B.ProjectionHom D)
    (A : Structure L Q) (α : Structure.Embedding A D) :
    B.toStructure.IsClosed (B.support α.toFunctionEmbedding) := by
  intro F x hx y hy
  have hargs : ∀ i, ∃ a : Q, B.part (x i) = α a := by
    intro i
    rcases hx i with ⟨a, ha⟩
    exact ⟨a, ha⟩
  choose a ha using hargs
  have hinput : B.part ∘ x = α ∘ a := by
    funext i
    exact ha i
  have hpartY : B.part y ∈ D.func F (B.part ∘ x) := by
    have himg :
        B.part y ∈ Structure.imageSet B.part (B.func F x) :=
      ⟨y, hy, rfl⟩
    rw [hB.2 F x] at himg
    exact himg
  have hpartY' : B.part y ∈ D.func F (α ∘ a) := by
    rw [← hinput]
    exact hpartY
  rw [← α.map_func F a] at hpartY'
  rcases hpartY' with ⟨b, hb, hby⟩
  exact ⟨b, hby.symm⟩

/-- Restrict to the parts selected by a full embedding alpha:A -> D. -/
noncomputable def restrict
    (B : System L P V) (D : Structure L P)
    (hB : B.ProjectionHom D)
    (A : Structure L Q) (α : Structure.Embedding A D) :
    System L Q (B.support α.toFunctionEmbedding) where
  toStructure := B.toStructure.induce
    (B.support α.toFunctionEmbedding)
    (support_closed B D hB A α)
  part := B.restrictedPart α.toFunctionEmbedding
  relTransversal R x hx i j hp := by
    apply Subtype.ext
    apply B.relTransversal R (Subtype.val ∘ x) hx i j
    exact (B.restrictedPart_spec α.toFunctionEmbedding (x i)).symm.trans
      ((congrArg α hp).trans
        (B.restrictedPart_spec α.toFunctionEmbedding (x j)))
  funcTransversal F x y z hy hz hp := by
    apply Subtype.ext
    apply B.funcTransversal F (Subtype.val ∘ x) y.1 z.1 hy hz
    exact (B.restrictedPart_spec α.toFunctionEmbedding y).symm.trans
      ((congrArg α hp).trans
        (B.restrictedPart_spec α.toFunctionEmbedding z))

/-- Restriction projects homomorphically to the source A. -/
theorem restrict_projectionHom
    (B : System L P V) (D : Structure L P)
    (hB : B.ProjectionHom D)
    (A : Structure L Q) (α : Structure.Embedding A D) :
    (B.restrict D hB A α).ProjectionHom A := by
  let E := B.restrict D hB A α
  constructor
  · intro R x hx
    have hD : D.rel R (B.part ∘ (Subtype.val ∘ x)) :=
      hB.1 R (Subtype.val ∘ x) hx
    have heq : α ∘ (E.part ∘ x) =
        B.part ∘ (Subtype.val ∘ x) := by
      funext i
      exact B.restrictedPart_spec α.toFunctionEmbedding (x i)
    have htarget : D.rel R (α ∘ (E.part ∘ x)) := by
      rw [heq]
      exact hD
    exact (α.map_rel_iff R (E.part ∘ x)).mp htarget
  · intro F x
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hpartY : B.part y.1 ∈
          D.func F (B.part ∘ (Subtype.val ∘ x)) := by
        have himg :
            B.part y.1 ∈
              Structure.imageSet B.part
                (B.func F (Subtype.val ∘ x)) :=
          ⟨y.1, hy, rfl⟩
        rw [hB.2 F (Subtype.val ∘ x)] at himg
        exact himg
      have heq : α ∘ (E.part ∘ x) =
          B.part ∘ (Subtype.val ∘ x) := by
        funext i
        exact B.restrictedPart_spec α.toFunctionEmbedding (x i)
      have hpartY' : α (E.part y) ∈
          D.func F (α ∘ (E.part ∘ x)) := by
        rw [heq, B.restrictedPart_spec α.toFunctionEmbedding y]
        exact hpartY
      rw [← α.map_func F (E.part ∘ x)] at hpartY'
      rcases hpartY' with ⟨b, hb, hab⟩
      exact α.injective hab ▸ hb
    · intro ha
      have himgA :
          α a ∈ Structure.imageSet α (A.func F (E.part ∘ x)) :=
        ⟨a, ha, rfl⟩
      rw [α.map_func F (E.part ∘ x)] at himgA
      have heq : α ∘ (E.part ∘ x) =
          B.part ∘ (Subtype.val ∘ x) := by
        funext i
        exact B.restrictedPart_spec α.toFunctionEmbedding (x i)
      rw [heq, ← hB.2 F (Subtype.val ∘ x)] at himgA
      rcases himgA with ⟨y, hy, hpart⟩
      have hySupp : y ∈ B.support α.toFunctionEmbedding := by
        exact ⟨a, hpart.symm⟩
      let ys : B.support α.toFunctionEmbedding := ⟨y, hySupp⟩
      refine ⟨ys, hy, ?_⟩
      apply α.injective
      exact (B.restrictedPart_spec α.toFunctionEmbedding ys).trans hpart

/-- Relabelling along a full embedding preserves the projection homomorphism. -/
theorem relabel_projectionHom
    (B : System L P V) (A : Structure L P)
    (hB : B.ProjectionHom A)
    (D : Structure L Q) (α : Structure.Embedding A D) :
    (B.relabel α.toFunctionEmbedding).ProjectionHom D := by
  change B.toStructure.IsHomomorphism D (α ∘ B.part)
  exact α.isHomomorphism.comp hB

end System

namespace Embedding

def relabel {B : System L P V} {W : Type*} {D : System L P W}
    (f : Embedding B D) (α : P ↪ Q) :
    Embedding (B.relabel α) (D.relabel α) where
  toEmbedding := f.toEmbedding
  map_part x := congrArg α (f.map_part x)

end Embedding

end StructuralRamsey.FunctionalPartite
