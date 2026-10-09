import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-! # From closed generating rank to the original weak tested vertices

The rank invariant controls U-closed substructures, whereas local
finiteness tests all small vertex subsets. For any property inherited
under full relational embeddings, the generating-rank bound on the
closed hull supplies that property on the original weak induced test.

The explicit restriction hypothesis below must be proved for the chosen
completion notion. It is not an axiom, and no equivalence of competing
U-irreducibility conventions is assumed in this module.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Positive bridge needed between the rank induction and local
finiteness: a hereditary property on all U-closed substructures of
U-size at most n holds on every weak test of at most n vertices.
The temporary hull may be larger than n; its generating rank is not. -/
theorem local_property_of_closed_USize
    [Finite V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hA : IsUClosed rules A)
    (Q : {W : Type v} → RelStructure L W → Prop)
    (hRestrict : ∀ {X Y : Type v}
      (E : RelStructure L X) (D : RelStructure L Y),
      Embedding E D → Q D → Q E)
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (A.induce T) →
      USize rules (A.induce T) ≤ n → Q (A.induce T))
    (S : Finset V) (hS : S.card ≤ n) :
    Q (A.induce (↑S : Set V)) := by
  classical
  let T : Set V := UClosureHull rules A (↑S : Set V)
  letI : Fintype T := Fintype.ofFinite T
  have hClosed : IsUClosed rules (A.induce T) :=
    hA.induce_UClosureHull (↑S : Set V)
  have hSize : USize rules (A.induce T) ≤ n :=
    (USize_induce_UClosureHull_le rules A S).trans hS
  have hQT : Q (A.induce T) := hRank T hClosed hSize
  let e : Embedding (A.induce (↑S : Set V)) (A.induce T) := {
    toFun := fun x =>
      ⟨x.1, subset_UClosureHull rules A (↑S : Set V) x.2⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  exact hRestrict (A.induce (↑S : Set V)) (A.induce T) e hQT

end StructuralRamsey.RelStructure
