import PartiteConstruction.Structure.GenericUGraphPartite
import PartiteConstruction.Partite.Induced

/-!
# Literal Hales–Jewett coordinate powers under the generic U-graph reindex

A partite system B and its reindex Bᵍ have exactly the same vertex carrier
and part map. The tagged power vertices are therefore equivalent on the
nose in their coordinates, including zero-dimensional powers and empty parts.

The actual induced coordinate power is computed by evaluating each relation
in every coordinate. Reindexing the original power is thus equivalent to
taking the induced power of the reindexed system, with no replacement by an
abstract Ramsey witness. No Ramsey hypothesis is assumed here.
-/

namespace StructuralRamsey.Partite

universe u v w

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

namespace NonInduced.Vertex

/-- Exact same-part, same-coordinate equivalence between tagged power
vertices for the original and reindexed partite systems. -/
noncomputable def uGraphEquiv
    (B : Partite.System L P V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) (N : ℕ) :
    NonInduced.Vertex B N ≃
      NonInduced.Vertex (B.asReducedUGraph U hU) N where
  toFun x := {
    part := x.part
    coord := x.coord
    belongs := x.belongs
  }
  invFun x := {
    part := x.part
    coord := x.coord
    belongs := x.belongs
  }
  left_inv := by
    intro x
    apply NonInduced.Vertex.ext B
    · rfl
    · intro i
      rfl
  right_inv := by
    intro x
    apply NonInduced.Vertex.ext (B.asReducedUGraph U hU)
    · rfl
    · intro i
      rfl

@[simp] theorem uGraphEquiv_part
    (B : Partite.System L P V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) (N : ℕ)
    (x : NonInduced.Vertex B N) :
    (uGraphEquiv B U hU N x).part = x.part := rfl

@[simp] theorem uGraphEquiv_coord
    (B : Partite.System L P V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) (N : ℕ)
    (x : NonInduced.Vertex B N) (i : Fin N) :
    (uGraphEquiv B U hU N x).coord i = x.coord i := rfl

end NonInduced.Vertex

namespace Induced

/-- The ACTUAL coordinatewise partite-power relation commutes with
the arbitrary-(L,U) symbol and tuple reindexing. This also covers N=0,
whose coordinatewise relation test is vacuous on both sides. -/
theorem power_reindex_rel_iff
    (B : Partite.System L P V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ)
    (S : (L.withUFunctionsReduced U).graph.Symbol)
    (t : Fin ((L.withUFunctionsReduced U).graph.arity S) →
      NonInduced.Vertex B N) :
    ((power B N).asReducedUGraph U hU).rel S t ↔
      (power (B.asReducedUGraph U hU) N).rel S
        (fun i => NonInduced.Vertex.uGraphEquiv B U hU N (t i)) :=
  Iff.rfl

/-- The underlying part label is literally preserved at every tagged
vertex, independently of N and the interpretations of U-relations. -/
theorem power_reindex_part
    (B : Partite.System L P V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ) (x : NonInduced.Vertex B N) :
    (power (B.asReducedUGraph U hU) N).part
      (NonInduced.Vertex.uGraphEquiv B U hU N x) =
      (power B N).part x :=
  rfl

end Induced
end StructuralRamsey.Partite
