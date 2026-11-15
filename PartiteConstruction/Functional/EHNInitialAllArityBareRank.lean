import PartiteConstruction.Functional.EHNInitialAllArityStrictTree
import PartiteConstruction.Functional.WeakAmbientACopyTraceRestorationBudget

/-!
# Track D: the all-arity genuine strict initial Picture has every bare rank

English proof committed FIRST:
docs/track-d-english-all-arity-initial-bare-locality-20261115.md

The checked all-arity initial Stage (including nullary function
outputs and nonempty canonical nullary gluing roots) is a
genuine STRICT full-functional tree of Base-copies.
Thus on EVERY literal weak test its restricted identity is an
ambient-relative weak HE into this same strict tree.
The initial rank bound is arbitrary; no control predecessor
or fake empty-root hypothesis is needed.

This supplies one stage predicate endpoint for the
independently still-conditional bare native HJ Picture route.
It does NOT supply the larger fixed control rank F_A(m)
required by that route.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- An actual all-arity native initial Picture of every genuine
FULL Base-placement into D is a strict full-functional tree
and therefore satisfies BARE ambient-relative weak-tree
locality for ANY finite test bound n.

In particular nullary source functions are allowed and their
canonical full nullary root is not replaced by an empty root.
The original control D is arbitrary and has no locality
assumption; the strict target is the initial Stage itself. -/
theorem initial_allArity_bareRank
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V] [Finite P]
    (hmBase : K Base)
    (hBase : Base.Irreducible)
    (beta0 : Structure.Embedding Base D) (n : ℕ) :
    ∃ T : Stage K D,
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base T.system.toStructure n ∧
      ∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  obtain ⟨T, hTree, hCopies⟩ :=
    initial_allArity_tree hK Base hmBase hBase beta0
  refine ⟨T, ?_, hCopies⟩
  intro S _hS
  let f : (↑S : Set T.Carrier) → T.Carrier := fun x => x.1
  have hf : IsAmbientRelativeWeakHE
      T.system.toStructure (↑S : Set T.Carrier)
      T.system.toStructure f :=
    (Structure.Embedding.id T.system.toStructure).ambientRelativeWeakRestriction
      (↑S : Set T.Carrier)
  exact ⟨T.Carrier, T.system.toStructure, hTree, f, hf⟩

end StructuralRamsey.FunctionalPartite.EHN
