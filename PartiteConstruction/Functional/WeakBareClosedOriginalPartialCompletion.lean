import PartiteConstruction.Functional.WeakAmbientACopyTraceRestorationBudget
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Track D: exact BARE strict weak-tree bound gives the 2019 closed result

English proof committed FIRST:
docs/track-d-english-bare-closed-original2019-20261115.md

A genuine strict full-functional Base-tree ambient-relative weak HE
on an exact finite weak test S upgrades on the SAME source vertices
to an ORIGINAL-2019 PARTIAL homomorphism-embedding whenever S
is FULLY function-closed in the original ambient source C.

This conclusion preserves all complete multivalued source-defined
fibres but NEVER asserts domain reflection of source-undefined
primitive function inputs. It is not the later total-fibre
`HasTreeCompletion`. The hard outer control-rank selection for
the optional native full-function HJ iteration is separate.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {VB W : Type v}

/-- The intended ORIGINAL-2019 partial-function local strict B-tree
conclusion of the weaker BARE strict functional weak-tree rank bound.

On a LITERAL finite fully function-closed source test S, the
ambient-relative weak map becomes the genuine original-partial
homomorphism-embedding on the FULL induced source C|S without
adding closure vertices, reflecting undefined input domains,
or replacing the strict FULL-functional target by a graph tree. -/
theorem AtMostBare.closedTest_originalPartialCompletion
    {Base : Structure L VB} {C : Structure L W}
    (n : ℕ) (hBare : AtMostBare Base C n)
    (S : Finset W) (hCard : S.card ≤ n)
    (hClosed : C.IsClosed (↑S : Set W)) :
    HasOriginalPartialTreeCompletion
      Base (C.induce (↑S : Set W) hClosed) := by
  obtain ⟨Y, Target, hTree, g, hg⟩ := hBare S hCard
  have hPartial :
      IsOriginalPartialHomomorphismEmbedding
        (C.induce (↑S : Set W) hClosed) Target g :=
    hg.toOriginalPartialHE_of_closed hClosed
  exact ⟨Y, Target, hTree, g, hPartial⟩

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
