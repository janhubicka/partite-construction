import PartiteConstruction.Functional.WeakBarePictureLinesControlBudget
import PartiteConstruction.Functional.EHNInitialAllArityStrictTree
import PartiteConstruction.Functional.EHNInvariantConstruction

/-!
# Track D: one COMPLETE all-arity native Ramsey pass with paid bare rank

English proof first:
docs/track-d-english-all-arity-onepass-bare-budget-20261115.md

This packages the real strict all-arity initial EHN Stage (including
canonical full nullary function roots) and the genuine finite
unrestricted Hales--Jewett line Picture with BARE rank into the
already checked generic induced Ramsey construction.

The input fixed control D MUST have both the full-functional Ramsey
arrow and the larger independent rank F_A(m). This does not assert
an unconditional native n-pass theorem or a noncircular rank schedule.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P U VB : Type v}
variable {K : Structure.StructureClass (L := L)}

/-- A complete native all-arity induced Ramsey pass, conditional on
a genuinely high-rank Ramsey control D.

At rank m+1 the new EHN Stage retains a full-functional strict Base
tree for every exact weak test, and has the genuine full-language
Ramsey arrow. The class K and the EHN part projection to D are built
into the Stage. No positive-arity or weak-test closure assumption.

The high-rank control hypothesis is an independent input: its
existence is NOT derived from the ordinary Ramsey arrow. -/
theorem inducedConstruction_allArity_bareRank_of_controlBudget
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Fintype U]
    (hKA : K A) (hA : A.Irreducible)
    (Base : Structure L VB) [Finite VB]
    (hKB : K Base) (hBase : Base.Irreducible)
    (eAB : Structure.Embedding A Base)
    (D : Structure L P) [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ)
    (m : ℕ)
    (hControlBare :
      SetAmbientRelativeWeakTreeWitness.AtMostBare Base D
        (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := U) m)) :
    ∃ T : Stage K D,
      SetAmbientRelativeWeakTreeWitness.AtMostBare
        Base T.system.toStructure (m + 1) ∧
      Structure.Arrow A Base T.system.toStructure κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    SetAmbientRelativeWeakTreeWitness.AtMostBare
      Base T.system.toStructure (m + 1)
  apply inducedConstruction_preserving A Base D κ hRamsey Q
  · intro beta0
    obtain ⟨T, hTree, hCopies⟩ :=
      initial_allArity_tree hK Base hKB hBase beta0
    have hBare : Q T := by
      intro S _hS
      let f : (↑S : Set T.Carrier) → T.Carrier := fun x => x.1
      have hf : IsAmbientRelativeWeakHE
          T.system.toStructure (↑S : Set T.Carrier)
          T.system.toStructure f :=
        (Structure.Embedding.id T.system.toStructure).ambientRelativeWeakRestriction
          (↑S : Set T.Carrier)
      exact ⟨T.Carrier, T.system.toStructure, hTree, f, hf⟩
    exact ⟨T, hBare, hCopies⟩
  · intro Old alpha hOld
    exact pictureLemma_lines_preservingBareRank_of_controlBudget
      hK A hA hKA Base hBase eAB Old alpha m hOld hControlBare κ

end StructuralRamsey.FunctionalPartite.EHN
