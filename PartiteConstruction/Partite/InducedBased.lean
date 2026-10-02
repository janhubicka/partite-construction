import PartiteConstruction.Partite.InducedPicture

/-! # Based stages in the induced partite construction

The survey says that a stage is obtained from a positive coordinatewise power
by extending every embedding of the restricted previous picture through free
amalgamation. The canonical object built by `Picture.build` is exactly that
free attachment. We package "based" as isomorphism to this canonical object.
-/
namespace StructuralRamsey.Partite

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v}
variable {V : Type w} {W : Type z}

/-- Isomorphism of partite systems, preserving the partition map and all
relations in both directions. -/
structure SystemIso (A : System L P V) (B : System L P W) where
  toEquiv : V ≃ W
  map_part : ∀ x, B.part (toEquiv x) = A.part x
  map_rel_iff : ∀ R x, B.rel R (toEquiv ∘ x) ↔ A.rel R x

namespace SystemIso

/-- Forget the part map and view a partite-system isomorphism as an induced
embedding of the underlying relational structures. -/
def toRelEmbedding {A : System L P V} {B : System L P W}
    (h : SystemIso A B) :
    RelStructure.Embedding A.toRelStructure B.toRelStructure where
  toFun := h.toEquiv
  injective := h.toEquiv.injective
  map_rel_iff := h.map_rel_iff

def refl (A : System L P V) : SystemIso A A where
  toEquiv := Equiv.refl V
  map_part := fun _ => rfl
  map_rel_iff := fun _ _ => Iff.rfl

end SystemIso

namespace Induced

open RelStructure

variable {U : Type t}
variable (A : RelStructure L U) (D : RelStructure L P)
variable (B : System L P V) (α : RelStructure.Embedding A D)

/-- A partite system is `(B, α(A))`-based when it is isomorphic to the
canonical free attachment over a positive power of the restriction of `B`
to the parts in `α(A)`. -/
def BasedOn {X : Type*} (C : System L P X) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Nonempty
    (SystemIso C
      (Picture.build B α.toFunctionEmbedding
        (Induced.power (B.restrict α.toFunctionEmbedding) N)))

/-- The canonical Picture-Lemma output is based by definition. -/
theorem canonical_based (N : ℕ) (hN : 0 < N) :
    BasedOn A D B α
      (Picture.build B α.toFunctionEmbedding
        (Induced.power (B.restrict α.toFunctionEmbedding) N)) := by
  exact ⟨N, hN, ⟨SystemIso.refl _⟩⟩

end Induced
end StructuralRamsey.Partite
