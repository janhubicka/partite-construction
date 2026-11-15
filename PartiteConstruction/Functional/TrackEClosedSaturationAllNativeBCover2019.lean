import PartiteConstruction.Functional.TrackEAllNativeInternalBCover2019
import PartiteConstruction.Iterated.ProjectedBCopyClosedFiniteSaturation
import PartiteConstruction.Ramsey.Basic

/-!
# Track E: constructed finite U-closed B-saturation has FULL native clause (3)

One SAME C' after an actual closed-root Btag saturation simultaneously
retains tagged Ramsey arrow and selected control HE, preserves U-closedness
and external protected tests, has internal tagged Btag extension,
AND satisfies exact native Structure.IrreduciblesExtendTo on ALL
function-closed ordinary irreducible induced subsets of its decoded
original set-valued function structure. The native endpoint is obtained
from the ACTUAL source C' and not another unrelated covered witness.

No strict native B-trees, class-H membership, cross-profile-tag language
identification or historical total-fibre global HE are asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure.ProjectedBCopyControl

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {X W Q VA : Type v}

/-- The finite relational Btag saturation has FULL native internal
B-coverage for EVERY native irreducible function-closed substructure.
This is precisely clause (3) on the concrete decoded final witness. -/
theorem wholeMask_closedSaturation_allNativeIrreduciblesExtendTo
    (Base : PartialSetStructure L X) [Finite X]
    (basePart : X → P)
    (hTrans : FibreTransversal Base basePart)
    (hPos : L.PositiveFuncArity)
    (Orig : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    [Fintype W]
    (Control : RelStructure ((L.withParts P).wholeMaskTagLanguage P) Q)
    (pOrig : W → Q)
    (hOrigClosed : IsUClosed
      ((L.withParts P).wholeMaskClosureRules P) Orig)
    (hBaseClosed : IsUClosed
      ((L.withParts P).wholeMaskClosureRules P)
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hBaseHered : HereditarilyIrreducible
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hExternal : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test Orig →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart))
      Control)
    {K : StructureClass
      (L := (L.withParts P).wholeMaskTagLanguage P)}
    (hBaseK : K (wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hHer : ClosedUHereditary K
      ((L.withParts P).wholeMaskClosureRules P))
    (hKIrr : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      K Test → Test.Irreducible)
    (A : RelStructure ((L.withParts P).wholeMaskTagLanguage P) VA)
    (Color : Type*)
    (hArrow : StructuralRamsey.Arrow A
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart))
      Orig Color) :
    ∃ (V' : Type v) (_ : Finite V')
      (C' : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V')
      (j : Embedding Orig C') (pNew : V' → Q),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) C' ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      (∀ x : W, pNew (j x) = pOrig x) ∧
      (∀ {T : Type v}
        (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
        IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
        IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
        Embedding Test C' →
        Nonempty (Embedding Test
          (wholeMaskTagExpansion
            ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) ∧
      IrreduciblesExtendTo
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))
        C' ∧
      Structure.IrreduciblesExtendTo Base.collapseDomain
        (wholeMaskOriginalDecode C').collapseDomain ∧
      StructuralRamsey.Arrow A
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))
        C' Color := by
  classical
  let Btag : RelStructure
      ((L.withParts P).wholeMaskTagLanguage P) X :=
    wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)
  obtain ⟨V', hV', C', j, pNew, hCClosed, hPNew, hOld,
      hExtNew, hInternal⟩ :=
    ProjectedBCopyControl.build_closed_all
      Orig Btag Control pOrig
      hOrigClosed hBaseClosed hExternal hBaseHered hpOrig hControl
  have hNativeAll : Structure.IrreduciblesExtendTo
      Base.collapseDomain (wholeMaskOriginalDecode C').collapseDomain :=
    wholeMaskCovered_internalTaggedB_to_allNativeIrreducibles
      C' Base basePart hTrans hCClosed hPos
      hBaseK hHer hKIrr hExtNew hInternal
  exact ⟨V', hV', C', j, pNew, hCClosed, hPNew, hOld,
    hExtNew, hInternal, hNativeAll, hArrow.of_embedding j⟩

end StructuralRamsey.RelStructure
