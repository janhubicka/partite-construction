import PartiteConstruction.Functional.NativePowerExactTwelve
import PartiteConstruction.Functional.RankedTreeReduct
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import PartiteConstruction.Iterated.Ordered

/-! # Ordered targets retain the native functional power obstruction

Adding the distinguished binary linear order to the three-vertex
binary-function template makes its *function graph* hereditarily
irreducible. The order symbol does not affect the function fibres.

A strict full-function tree over any ordered expansion of a base with
irreducible functional reduct remains a strict functional tree after
forgetting the order. To see root containment after reduct, locate the
expanded irreducible root inside a constituent base copy first.

Consequently no map preserving complete function fibres from the old
native second power can enter a strict tree of the ordered template.
This does not yet construct the *ordered seven-vertex input stage* and
its EHN projection; those are a separate source-expansion obligation.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {V W : Type v}

/-- Forgetting the distinguished order preserves strict full-functional
B-trees when the function-language reduct of the base is irreducible.
Root containment is transferred via a constituent base copy, not by
assuming an arbitrary expanded irreducible witness remains irreducible
in the reduct. -/
theorem TreeAmalgam.linearOrderReduct
    {Base : Structure L.withLinearOrder V}
    {T : Structure L.withLinearOrder W}
    (hBase : Base.linearOrderReduct.Irreducible)
    (hT : TreeAmalgam Base W T) :
    TreeAmalgam Base.linearOrderReduct W T.linearOrderReduct := by
  induction hT with
  | copy e hsurj =>
      exact TreeAmalgam.copy e.linearOrderReduct hsurj
  | @glue W₁ W₂ Z W T₁ T₂ Root T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      have hc₁red :
          (f₁.linearOrderReduct).ContainedInIrreducible := by
        obtain ⟨Q,E,hE,j,hj⟩ := hc₁
        obtain ⟨k,hk⟩ := h₁.irreducible_contained_in_copy hE j
        refine ⟨V, Base.linearOrderReduct, hBase,
          k.linearOrderReduct, ?_⟩
        intro d
        obtain ⟨x,hdx⟩ := hj d
        obtain ⟨b,hxb⟩ := hk x
        exact ⟨b,hdx.trans hxb⟩
      have hc₂red :
          (f₂.linearOrderReduct).ContainedInIrreducible := by
        obtain ⟨Q,E,hE,j,hj⟩ := hc₂
        obtain ⟨k,hk⟩ := h₂.irreducible_contained_in_copy hE j
        refine ⟨V, Base.linearOrderReduct, hBase,
          k.linearOrderReduct, ?_⟩
        intro d
        obtain ⟨x,hdx⟩ := hj d
        obtain ⟨b,hxb⟩ := hk x
        exact ⟨b,hdx.trans hxb⟩
      exact TreeAmalgam.glue
        ih₁ ih₂ f₁.linearOrderReduct f₂.linearOrderReduct
        hc₁red hc₂red i₁.linearOrderReduct i₂.linearOrderReduct
        hfree.linearOrderReduct

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The canonical ordered expansion of the three-vertex template.
All three original roles remain unary, and the function is unchanged. -/
def toyBaseOrdered : Structure toyLanguage.withLinearOrder (Fin 3) :=
  toyBase.withLinearOrder

/-- Adding the ordinary pairwise order makes every *induced function
graph* substructure irreducible. The new binary relation itself
witnesses every pair of distinct vertices. -/
theorem toyBaseOrdered_graph_hereditarilyIrreducible :
    toyBaseOrdered.graph.HereditarilyIrreducible := by
  intro S x y hxy
  have hval : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  by_cases hlt : x.1 < y.1
  · refine ⟨(.inl (.inr ()) :
      toyLanguage.withLinearOrder.graph.Symbol), ?_⟩
    change ∃ (z : Fin 2 → S) (i j : Fin 2),
      (toyBaseOrdered.graph.induce S).rel (.inl (.inr ())) z ∧
      z i = x ∧ z j = y
    let z : Fin 2 → S := ![x,y]
    refine ⟨z,0,1,?_,rfl,rfl⟩
    change x.1 < y.1
    exact hlt
  · have hyx : y.1 < x.1 :=
      lt_of_le_of_ne (le_of_not_gt hlt) hval.symm
    refine ⟨(.inl (.inr ()) :
      toyLanguage.withLinearOrder.graph.Symbol), ?_⟩
    change ∃ (z : Fin 2 → S) (i j : Fin 2),
      (toyBaseOrdered.graph.induce S).rel (.inl (.inr ())) z ∧
      z i = x ∧ z j = y
    let z : Fin 2 → S := ![y,x]
    refine ⟨z,1,0,?_,rfl,rfl⟩
    change y.1 < x.1
    exact hyx

/-- The ordered expansion does not modify any relation/function in the
original language. -/
theorem toyBaseOrdered_reduct :
    toyBaseOrdered.linearOrderReduct = toyBase := rfl

/-- No full-fibre homomorphism from the actual native second power
can map into a strict full tree of the *ordered* template. This is
a target statement; the separately needed ordered EHN input stage is
not asserted here. -/
theorem actualPower_no_fullOrderedStrictTreeHom
    {W : Type} {T : Structure toyLanguage.withLinearOrder W}
    (hTree : TreeAmalgam toyBaseOrdered W T)
    (f : PowerVertex → W)
    (hf : actualPower.IsHomomorphism T.linearOrderReduct f) : False := by
  have hTreeRed :
      TreeAmalgam toyBase W T.linearOrderReduct := by
    simpa only [toyBaseOrdered_reduct] using
      hTree.linearOrderReduct toyBase_irreducible
  exact actualPower_no_fullStrictTreeHom hTreeRed f hf

end StructuralRamsey.Structure.NativePowerObstruction
