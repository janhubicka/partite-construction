import PartiteConstruction.Functional.EHNToRelationalPartite
import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Partite.InducedBased

/-! # Weak functional support restriction commutes with graph restriction

Native functional iterated Pictures select exactly the vertices whose
projection lies inside a full A-copy in D. Since this support is closed under
all *actual* function values, the native weak restriction is a genuine full
induced functional structure, though its projection need only be weak.

Passing to its function graph gives exactly the ordinary relational partite
restriction, up to identity on vertices. This theorem is an interface for
weak-substructure analysis, not a U-closed relational construction.
-/

namespace StructuralRamsey.FunctionalPartite.System

universe u v
variable {L : Language.{u}} {P U V : Type v}

/-- The genuine function-closed support restriction of an EHN system and the
induced restriction of its graph partite view are canonically isomorphic as
relational partite systems, including equality of their part maps. -/
noncomputable def weakRestrictGraphIso
    (B : FunctionalPartite.System L P V)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U)
    (α : Structure.Embedding A D) :
    Partite.SystemIso
      ((B.weakRestrict D hB.1 A α).toGraphPartite A
        (B.weakRestrict_invariant D hB.1 A α hB))
      ((B.toGraphPartite D hB).restrict α.toFunctionEmbedding) where
  toEquiv := Equiv.refl _
  map_part := by
    intro x
    rfl
  map_rel_iff := by
    intro R z
    cases R with
    | inl R => rfl
    | inr F => rfl

end StructuralRamsey.FunctionalPartite.System
