import PartiteConstruction.Functional.MixedSmallRootGeneratorBudget

/-!
# Functional irreducibility of a root with at most one vertex

For the genuine universal free-amalgamation notion, every structure
with at most one vertex is irreducible: in any free amalgam an embedded
point lies on one of its two sides, and the image of a subsingleton
carrier consists of at most that point. Empty carriers are trivial.

Together with the verified sharp generator-budget theorem for GENUINELY
mixed full-functional free amalgams whose root has at most one vertex,
this removes both problems of the small-root case:
  (1) each side stays n-generated;
  (2) their irreducible root admits the same prescribed Base embedding.

The strict relative synchronization itself is the independently
verified theorem from PR #286. Reducible roots necessarily contain
at least two vertices; their compatible side extension construction
remains the open maximal-mixed-root case.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {H : Type v}

/-- Any full relation/function structure on a subsingleton carrier is
irreducible in the universal, embedding-based free-amalgam sense. -/
theorem irreducible_of_subsingleton
    (Root : Structure L H) [Subsingleton H] :
    Root.Irreducible := by
  intro H' E' F' C' Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  classical
  by_cases hNE : Nonempty H
  · let x : H := Classical.choice hNE
    rcases hFree.covers (e x) with ⟨a, ha⟩ | ⟨b, hb⟩
    · left
      intro y
      refine ⟨a, ?_⟩
      calc
        e y = e x := congrArg e (Subsingleton.elim y x)
        _ = iE a := ha
    · right
      intro y
      refine ⟨b, ?_⟩
      calc
        e y = e x := congrArg e (Subsingleton.elim y x)
        _ = iF b := hb
  · left
    intro x
    exact (hNE ⟨x⟩).elim

/-- The convenient finite-cardinality interface for actual EHN closed
separators. A common root with ≤1 vertices is always function-language
irreducible, irrespective of relation or function arities. -/
theorem irreducible_of_card_le_one
    (Root : Structure L H) [Finite H]
    (hCard : Nat.card H ≤ 1) :
    Root.Irreducible := by
  letI : Subsingleton H :=
    (Finite.card_le_one_iff_subsingleton).mp hCard
  intro H' E' F' C' Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  exact (irreducible_of_subsingleton Root) hFree e

end StructuralRamsey.Structure
