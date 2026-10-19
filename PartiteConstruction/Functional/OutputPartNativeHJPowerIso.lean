import PartiteConstruction.Functional.OutputPartNativeHJPower

/-!
# Actual native positive Hales--Jewett power commutes with output-part split

A true native partite HJ power vertex consists of one part label
and a tuple of actual old-stage vertices in that part. Passing
to the (F,q)-singleton split retains EXACTLY these vertices.

For N>0, a new output (F,q) in the singleton split of the
TRUE native power is equivalent to requiring in EVERY coordinate
an original F-value lying in output part q. This is exactly the
(F,q)-fibre of the true coordinatewise power of the split stage.

The canonical coordinate/part identity therefore defines a
surjective FULL PART-PRESERVING functional embedding (hence a
full functional isomorphism) from the split native power to
the native power of the split stage, on the same exact vertex
set up to the canonical identity bijection.

No relational proxy, output ordering, generated closure,
change of parts, or nullary erasure is used. The assumption
N>0 is genuinely necessary: zero powers are a counterexample.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The canonical identity on part label and coordinates,
from an old native HJ power vertex to the corresponding
power vertex in the per-output-part singleton language. -/
def toSplitPowerVertex (B : System L P V) (N : ℕ) :
    Vertex B N → Vertex (B.splitOutputParts) N :=
  fun x => {
    part := x.part
    coord := x.coord
    belongs := x.belongs
  }

/-- Inverse of the canonical HJ power vertex presentation map.
The proof of part membership is definitionally identical because
the split System retains exactly the old part map. -/
def fromSplitPowerVertex (B : System L P V) (N : ℕ) :
    Vertex (B.splitOutputParts) N → Vertex B N :=
  fun x => {
    part := x.part
    coord := x.coord
    belongs := x.belongs
  }

@[simp] theorem toSplitPowerVertex_coord
    (B : System L P V) (N : ℕ)
    (x : Vertex B N) (i : Fin N) :
    (toSplitPowerVertex B N x).coord i = x.coord i := rfl

@[simp] theorem fromSplitPowerVertex_coord
    (B : System L P V) (N : ℕ)
    (x : Vertex (B.splitOutputParts) N) (i : Fin N) :
    (fromSplitPowerVertex B N x).coord i = x.coord i := rfl

/-- On every genuine POSITIVE-length native Hales--Jewett power,
splitting original multivalued function output fibres into (F,q)
is a FULL PARTITE EMBEDDING onto the HJ power of the split system.

This is literal entire output-fibre equality, including all
original multivalued outputs and their transversal output parts,
not an EHN/original-partial projection. -/
def splitPowerEmbedding
    (B : System L P V) (N : ℕ) (hN : 0 < N) :
    Embedding ((power B N).splitOutputParts)
      (power (B.splitOutputParts) N) where
  toEmbedding := {
    toFun := toSplitPowerVertex B N
    injective := by
      intro x y hxy
      apply Vertex.ext B
      · exact congrArg
          (fun t : Vertex (B.splitOutputParts) N => t.part) hxy
      · intro i
        exact congrFun (congrArg
          (fun t : Vertex (B.splitOutputParts) N => t.coord) hxy) i
    map_rel_iff := by
      intro R xs
      rfl
    map_func := by
      intro Fq xs
      rcases Fq with ⟨F, q⟩
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hCoordinate :=
          (power_splitOutputParts_func_iff
            B N hN F.down q xs z).mp hz
        change ∀ i : Fin N,
          (toSplitPowerVertex B N z).coord i ∈
            B.func F.down
              (fun j => ((toSplitPowerVertex B N ∘ xs) j).coord i) ∧
          B.part ((toSplitPowerVertex B N z).coord i) = q
        change ∀ i : Fin N,
          z.coord i ∈ B.func F.down (fun j => (xs j).coord i) ∧
          B.part (z.coord i) = q
        exact hCoordinate
      · intro hy
        let z : Vertex B N := fromSplitPowerVertex B N y
        have hCoord :
            ∀ i : Fin N,
              z.coord i ∈
                B.func F.down (fun j => (xs j).coord i) ∧
              B.part (z.coord i) = q := by
          change ∀ i : Fin N,
            y.coord i ∈
              B.func F.down
                (fun j => ((toSplitPowerVertex B N ∘ xs) j).coord i) ∧
            B.part (y.coord i) = q at hy
          change ∀ i : Fin N,
            y.coord i ∈ B.func F.down (fun j => (xs j).coord i) ∧
            B.part (y.coord i) = q at hy
          exact hy
        have hz :
            z ∈ ((power B N).splitOutputParts).func
              (F, q) xs :=
          (power_splitOutputParts_func_iff
            B N hN F.down q xs z).mpr hCoord
        refine ⟨z, hz, ?_⟩
        apply Vertex.ext (B.splitOutputParts)
        · rfl
        · intro i
          rfl
  }
  map_part := fun _ => rfl

/-- The displayed FULL partite embedding of genuine native HJ
power systems is SURJECTIVE, hence is an isomorphism of full
functional partite structures. Every target power vertex has
exactly the same part and coordinate tuple. -/
theorem splitPowerEmbedding_surjective
    (B : System L P V) (N : ℕ) (hN : 0 < N) :
    Function.Surjective (splitPowerEmbedding B N hN) := by
  intro y
  refine ⟨fromSplitPowerVertex B N y, ?_⟩
  apply Vertex.ext (B.splitOutputParts)
  · rfl
  · intro i
    rfl

end StructuralRamsey.FunctionalPartite.Induced
