import PartiteConstruction.Functional.EHNToRelationalPartite
import PartiteConstruction.Functional.Induced
import PartiteConstruction.Iterated.LocalTreeLike

/-! # The genuine functional Hales--Jewett power has the expected graph

The native function-language power uses actual set-valued functions;
its graph is (isomorphic to) the ordinary coordinatewise relational power
of the graph-partite view of the native previous stage.  This is an
**interpretation lemma for weak tests**, not a replacement of the genuine
functional power by the recursive U-closed construction.

The tagged product vertex types have exactly the same part and coordinate
information. The result holds with only an EHN weak global projection.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- Canonical identification of the two tagged powers, without imposing
U-closedness on their embeddings or any fibre-surjectivity on projection. -/
def vertexGraphEquiv
    (B : FunctionalPartite.System L P V)
    (D : Structure L P) (hB : B.WeaklyPartiteOver D)
    (N : ℕ) :
    Vertex B N ≃
      Partite.Induced.Vertex (B.toGraphPartite D hB) N where
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
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- Passing to the function graph commutes with coordinatewise Hales--Jewett
power, up to the trivial identification of tagged product vertex types. -/
def powerGraphIso
    (B : FunctionalPartite.System L P V)
    (D : Structure L P) (hB : B.WeaklyPartiteOver D)
    (N : ℕ) :
    RelStructure.Iso
      ((power B N).toStructure.graph)
      ((Partite.Induced.power (B.toGraphPartite D hB) N).toRelStructure) where
  toEquiv := vertexGraphEquiv B D hB N
  map_rel_iff := by
    intro R z
    cases R with
    | inl R =>
        rfl
    | inr F =>
        rfl

end StructuralRamsey.FunctionalPartite.Induced
