import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Relational.Order

/-! # Ordered structures are hereditarily irreducible

The distinguished strict linear order makes every induced substructure
irreducible: any two distinct vertices occur together in an order tuple.
This is the hypothesis needed by the straightforward gluing proof of the
survey's strengthened tree invariant.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Every induced substructure of a genuinely linearly ordered expansion is
irreducible. -/
theorem ordered_hereditarilyIrreducible
    (A : RelStructure L V) [LinearOrder V] :
    HereditarilyIrreducible A.ordered := by
  intro S x y hxy
  have hval : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  by_cases hlt : x.1 < y.1
  · let z : Fin 2 → S := ![x, y]
    refine ⟨.inr (), z, 0, 1, ?_, rfl, rfl⟩
    change x.1 < y.1
    exact hlt
  · have hyx : y.1 < x.1 :=
      lt_of_le_of_ne (le_of_not_gt hlt) hval.symm
    let z : Fin 2 → S := ![y, x]
    refine ⟨.inr (), z, 1, 0, ?_, rfl, rfl⟩
    change y.1 < x.1
    exact hyx

end StructuralRamsey.RelStructure
