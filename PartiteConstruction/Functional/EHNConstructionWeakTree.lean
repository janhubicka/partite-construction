import PartiteConstruction.Functional.EHNInitialWeakTree
import PartiteConstruction.Functional.EHNPictureWeakTree
import PartiteConstruction.Functional.EHNInvariantConstruction

/-! # One complete genuine-functional EHN Ramsey pass raises weak-tree rank

The positive-arity EHN Ramsey step uses the ordinary full functional
Hales--Jewett power, closed support restriction, and full functional free
amalgams.  The weak graph-tree induction is only an auxiliary predicate
on the genuine stages: no intermediate U-closed relational construction
is substituted for them.

The separately validated generic EHN canonicalization and backward
colour extraction transport the predicate through the entire pass.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}

/-- One whole class-preserving induced functional partite pass increases the
rank of the controlled weak-substructure graph-tree invariant by one, while
retaining the full function-language Ramsey arrow. -/
theorem inducedConstruction_weakGraphLocallyTreeLike
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph B.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph B.graph
        T.system.toStructure.graph n ∧
      Structure.Arrow A B T.system.toStructure κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    RelStructure.LocallyTreeLike A.graph B.graph T.system.toStructure.graph n
  have hInitial :
      ∀ β₀ : Structure.Embedding B D,
        ∃ S : Stage K D,
          Q S ∧
          ∀ β : Structure.Embedding B D,
            ∃ j : Structure.Embedding B S.system.toStructure,
              ∀ x, S.system.part (j x) = β x := by
    intro β₀
    exact initial_weakGraphLocallyTreeLike
      hK A B hKB hA eAB hpos β₀ n hn hD
  have hStep :
      ∀ (S : Stage K D) (α : Structure.Embedding A D),
        Q S →
        ∃ R : Stage K D,
          Q R ∧ PictureProperty A S R α κ := by
    intro S α hS
    exact pictureLemma_weakGraphLocallyTreeLike
      hK A hKA B hA eAB S α κ n hn hD hS
  exact inducedConstruction_preserving
    A B D κ hRamsey Q hInitial hStep

end StructuralRamsey.FunctionalPartite.EHN
