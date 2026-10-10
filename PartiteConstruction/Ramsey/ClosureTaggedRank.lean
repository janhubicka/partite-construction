import PartiteConstruction.Ramsey.ClosureTaggedClosedMap
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-! # Exact closure hull and generating rank under tagged part expansions

Root-tagging the closure-relation symbols does not change the family
of relative U-substructures on ANY exact vertex set. Therefore it
does not change the closure operator, which is the intersection of
all relative U-substructures containing a given set.

The induced restriction on an exact carrier commutes definitionally
with expansion, and the smallest number of U-generating vertices
(USize, published Definition 2.25) is exactly preserved, without
closedness or finiteness of the ambient structure except for the
Fintype needed to DEFINE USize.

These statements do not bound the number of vertices in a generated
hull, do not change the weak test carrier, and do not prove the
remaining Picture rank-increment construction.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V P : Type v}

/-- Expand an induced structure using the restricted part map, or
restrict the expanded structure: both give literally the same full
relations, even for nonclosed weak subsets and nullary tuples. -/
theorem expandTaggedClosureParts_induce
    (rules : ClosureDescription L) (A : RelStructure L V)
    (part : V → P) (S : Set V) :
    (RelStructure.expandTaggedClosureParts rules A part).induce S =
      RelStructure.expandTaggedClosureParts rules (A.induce S)
        (fun x : S => part x.1) := by
  have hRel :
      ((RelStructure.expandTaggedClosureParts rules A part).induce S).rel =
        (RelStructure.expandTaggedClosureParts rules (A.induce S)
          (fun x : S => part x.1)).rel := by
    funext R z
    cases R with
    | inl R => rfl
    | inr R =>
      cases R with
      | inl tag => rfl
      | inr p => rfl
  exact congrArg (fun rel =>
    (RelStructure.mk rel :
      RelStructure (L.withTaggedClosureParts rules P) S)) hRel

/-- Exact equality of closure operators on the original vertex set.
The source need not be closed. In particular root-tagging introduces
no new generators and no new closure outputs. -/
theorem UClosureHull_taggedParts_eq
    (rules : ClosureDescription L) (A : RelStructure L V)
    (part : V → P) (S : Set V) :
    UClosureHull (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) S =
      UClosureHull rules A S := by
  ext x
  constructor
  · intro hx T hT hST
    exact hx T ((isUSubstructure_iff_taggedParts rules A part T).mp hT) hST
  · intro hx T hT hST
    exact hx T ((isUSubstructure_iff_taggedParts rules A part T).mpr hT) hST

/-- Generating sets are exactly the same under the tagged expansion,
including weak nonclosed sources and empty generating sets. -/
theorem isUGenerating_taggedParts_iff
    (rules : ClosureDescription L) (A : RelStructure L V)
    (part : V → P) (S : Set V) :
    IsUGenerating (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) S ↔
      IsUGenerating rules A S := by
  change
    UClosureHull (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) S = Set.univ ↔
      UClosureHull rules A S = Set.univ
  rw [UClosureHull_taggedParts_eq]

/-- The published U-size (MINIMUM GENERATING SUPPORT CARDINALITY)
is exactly invariant under root-tagged part expansion. The generated
hull itself may be larger, and the original weak subset is not
replaced by its hull. -/
theorem USize_taggedParts_eq
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (part : V → P) :
    USize (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) =
      USize rules A := by
  classical
  let TagA := RelStructure.expandTaggedClosureParts rules A part
  let TagU := rules.withTaggedClosureParts P
  obtain ⟨S, hCardS, hGenS⟩ := USize_spec rules A
  have hLE : USize TagU TagA ≤ USize rules A := by
    calc
      USize TagU TagA ≤ S.card :=
        USize_le_of_generating TagU TagA S
          ((isUGenerating_taggedParts_iff rules A part (↑S : Set V)).mpr hGenS)
      _ = USize rules A := hCardS
  obtain ⟨T, hCardT, hGenT⟩ := USize_spec TagU TagA
  have hGE : USize rules A ≤ USize TagU TagA := by
    calc
      USize rules A ≤ T.card :=
        USize_le_of_generating rules A T
          ((isUGenerating_taggedParts_iff rules A part (↑T : Set V)).mp hGenT)
      _ = USize TagU TagA := hCardT
  exact Nat.le_antisymm hLE hGE

end StructuralRamsey.RelStructure
