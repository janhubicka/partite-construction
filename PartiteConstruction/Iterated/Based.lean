import PartiteConstruction.Iterated.Step
import PartiteConstruction.Partite.InducedBased

/-! # Local tree-likeness across based induced steps

The induced trace records each successor only up to partite-system isomorphism
with the canonical Picture build.  Local tree-likeness is pulled back along
the relational embedding underlying that isomorphism.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- Forget the partition data of a partite-system isomorphism. -/
def Partite.SystemIso.toRelEmbedding
    {C : Partite.System L P X} {D : Partite.System L P Y}
    (h : Partite.SystemIso C D) :
    RelStructure.Embedding C.toRelStructure D.toRelStructure where
  toFun := h.toEquiv
  injective := h.toEquiv.injective
  map_rel_iff := h.map_rel_iff

/-- Any based successor step preserves local tree-likeness under the
hypotheses of the canonical one-step theorem. -/
theorem basedStep_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (C₁ : Partite.System L P Y)
    (α : RelStructure.Embedding A D)
    [Finite U] [Finite V] [Finite P] [Finite X]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hC₀ : RelStructure.LocallyTreeLike A B C₀.toRelStructure n)
    (hPartite : C₀.IsPartiteOver D)
    (hBased : Partite.Induced.BasedOn A D C₀ α C₁) :
    RelStructure.LocallyTreeLike A B C₁.toRelStructure n := by
  rcases hBased with ⟨N, hN, hIso⟩
  let αf := α.toFunctionEmbedding
  let R := C₀.restrict αf
  let E := Partite.Induced.power R N
  let Canon := Partite.Picture.build C₀ αf E
  have hCanon :
      RelStructure.LocallyTreeLike A B Canon.toRelStructure n := by
    exact canonicalStep_locallyTreeLike
      A B D C₀ α hA eAB n hn hD hC₀ hPartite N hN
  let iso : Partite.SystemIso C₁ Canon := Classical.choice hIso
  exact hCanon.pullback_embedding iso.toRelEmbedding

end StructuralRamsey.Partite.Iterated
