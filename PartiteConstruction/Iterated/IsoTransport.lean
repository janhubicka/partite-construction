import PartiteConstruction.Iterated.LocalTreeLike

/-! # Transporting local homomorphism-embeddings across a tree-stage iso

The actual functional EHN attachment has a graph isomorphism to a
relational free attachment of the same copies.  To reuse the relational
projected weak-tree induction, we transport its projection to the target
control along the inverse of that isomorphism.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W X : Type v}
variable {A : RelStructure L V} {B : RelStructure L W}
variable {D : RelStructure L X}

namespace Iso

/-- A relational isomorphism also induces an embedding in the other
direction; the full relation-reflection condition follows by evaluating
the source isomorphism on the inverse tuple. -/
def toInverseEmbedding (h : Iso A B) : Embedding B A where
  toFun := h.toEquiv.symm
  injective := h.toEquiv.symm.injective
  map_rel_iff := by
    intro R z
    have hrel :=
      h.map_rel_iff R (h.toEquiv.symm ∘ z)
    have hcomp : h.toEquiv ∘ (h.toEquiv.symm ∘ z) = z := by
      funext i
      exact h.toEquiv.apply_symm_apply (z i)
    rw [hcomp] at hrel
    exact hrel.symm

end Iso

/-- Transfer a homomorphism-embedding projection to a control structure
across an isomorphic re-presentation of a stage. -/
theorem IsHomomorphismEmbedding.transportIso
    {p : V → X}
    (hp : A.IsHomomorphismEmbedding D p)
    (h : Iso A B) :
    B.IsHomomorphismEmbedding D (p ∘ h.toEquiv.symm) :=
  hp.comp h.toInverseEmbedding.isHomomorphismEmbedding

end StructuralRamsey.RelStructure
