import PartiteConstruction.Ramsey.ClosureProtectedPicture

/-! # The exponent-one protected power case

The native coordinatewise induced power at exponent one is canonically
isomorphic to the original partite structure. In particular the working
protected part projection survives this power, without any hereditary
irreducibility assumption.

This serves as a checked base/regression. For Hales--Jewett exponents
N > 1, the analogous protected projection is not a consequence of
the exponent-one argument and remains a separate proof obligation.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P V : Type v}

/-- Coordinate evaluation at the unique position is an induced embedding
of the native one-coordinate power into the original structure. -/
def powerOneEmbedding (B : System L P V) :
    RelStructure.Embedding (power B 1).toRelStructure B.toRelStructure where
  toFun := fun x => x.coord 0
  injective := by
    intro x y hxy
    apply NonInduced.Vertex.ext B
    · calc
        x.part = B.part (x.coord 0) := (x.belongs 0).symm
        _ = B.part (y.coord 0) := congrArg B.part hxy
        _ = y.part := y.belongs 0
    · intro k
      have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hk]
      exact hxy
  map_rel_iff := by
    intro R x
    change B.rel R (fun j => (x j).coord (0 : Fin 1)) ↔
      (∀ k : Fin 1, B.rel R (fun j => (x j).coord k))
    constructor
    · intro h k
      have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hk]
      exact h
    · intro h
      exact h 0

/-- Protected projection of the old partite system suffices for the
one-coordinate power. This is not asserted for arbitrary exponents. -/
theorem power_one_isClosedPartiteOver
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V)
    (hB : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure A B.part) :
    IsClosedUHomomorphismEmbedding rules
      (power B 1).toRelStructure A (power B 1).part := by
  have hMap : IsClosedUHomomorphismEmbedding rules
      (power B 1).toRelStructure A
      (fun x => B.part (x.coord (0 : Fin 1))) :=
    hB.comp ((powerOneEmbedding B).isClosedUHomomorphismEmbedding rules)
  have hEq :
      (fun x : Vertex B 1 => B.part (x.coord (0 : Fin 1))) =
        (power B 1).part := by
    funext x
    exact x.belongs 0
  rw [← hEq]
  exact hMap

end StructuralRamsey.Partite.Induced
