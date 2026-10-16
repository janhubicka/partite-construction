import PartiteConstruction.Functional.EHNLineOnlyPicture
import PartiteConstruction.Functional.EHNInvariantConstruction

set_option autoImplicit false

/-!
# An entire native functional induced Ramsey pass using only HJ LINE attachments

The independently validated recursive Ramsey theorem supplies an
arbitrary full-function control D (not necessarily a class member).
The verified EHN initial stage puts a full B-copy over every B-placement
of D, with the canonical shared nullary root for zero-arity functions.

The new HJ line-indexed Picture lemma suffices for each of the finite
A-placement canonicalization steps. Consequently the usual finite
backwards colouring argument yields a complete induced Ramsey pass,
without attaching old-stage copies along the larger family of all
arbitrary selected-support embeddings into each power.

All intermediate stages are genuine systems of set-valued functions.
Each operation-output image stays TRANSVERSAL with the part map;
all A- and B-copies used by the Ramsey arrow are FULL embeddings.
No U-closed relational replay or global reflection of undefined
function domains is introduced.

This theorem confirms that narrowing the attachment family does not
lose the ordinary Ramsey conclusion. It is NOT the still-open strict
functional sparsening theorem: additional weak-test B-tree locality
must be preserved across several distinct HJ line attachments.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- One class-preserving induced functional Ramsey pass with
ARBITRARY function arities, performed using only full Hales-Jewett
LINE attachments in every Picture step.

The entire construction is native functional and every intermediate
partite-system operation fibre remains part-transversal. -/
theorem inducedConstruction_allArity_lines
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ) :
    ∃ T : Stage K D,
      Structure.Arrow A B T.system.toStructure κ := by
  obtain ⟨T, _hTrue, hArrow⟩ :=
    inducedConstruction_preserving
      A B D κ hRamsey
      (fun _ : Stage K D => True)
      (fun beta0 => by
        obtain ⟨S, hCopies⟩ := initial_allArity hK B hB beta0
        exact ⟨S, trivial, hCopies⟩)
      (fun S alpha _hS => by
        obtain ⟨R, hPicture⟩ :=
          pictureLemma_lines hK A hA S alpha κ
        exact ⟨R, trivial, hPicture⟩)
  exact ⟨T, hArrow⟩

end StructuralRamsey.FunctionalPartite.EHN
