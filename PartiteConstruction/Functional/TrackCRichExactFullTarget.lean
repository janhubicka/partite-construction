import PartiteConstruction.Functional.TrackCOptionFullExactRange
import PartiteConstruction.Functional.TrackEClosedExactTaggedTestEmbedding2019
import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Appendix A Track C: EXACT rich Option(Set) H-target copy, selected same map

This is the genuinely rich analogue of the native no-defined-empty
test proof. The original full test E is a PartialSetStructure with
independent domain bits and possible some(empty) values.

The actual first-stage U-closed tagged witness is NOT assumed
canonical. For a full genuinely partial embedding g:E->P into its
actual decoder P and a full selected OLD tag-test map
jTag:C.induce(range g)->tag(Target), compose the exact FULL-image
factor and the checked exact tagged-to-partial full decoder.

This yields a full ORIGINAL Option(Set) embedding of E into the SAME
Target, on exactly the original map jTag o g; no collapseDomain,
NoDefinedEmptyValues, closure hull, source replacement or extra bound.
It does NOT supply existence or simultaneous coherence of selected
H completions, nor prove the full Appendix A class theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q Y T : Type v}

/-- A genuine full source test inside the ACTUAL covered tagged
two-pass witness, together with the full selected exact OLD tagged
test map, has a FULL genuine partial completion on the composite
same vertex map. Defined-empty source inputs are retained. -/
noncomputable def wholeMaskCovered_exactRichPartialTest_toFullTarget
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (E : PartialSetStructure L T)
    (g : PartialSetStructure.Embedding E (wholeMaskOriginalDecode C))
    (Target : PartialSetStructure L Y) [Finite Y]
    (targetPart : Y → Parts)
    (hTr : FibreTransversal Target targetPart)
    (jTag : Embedding (C.induce (Set.range g.toFun))
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart))) :
    ∃ k : PartialSetStructure.Embedding E Target,
      ∀ x : T,
        k.toFun x = jTag.toFun ⟨g.toFun x, ⟨x, rfl⟩⟩ := by
  classical
  let P : PartialSetStructure L V := wholeMaskOriginalDecode C
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let S : Set V := Set.range g.toFun
  have hOriginalClosed : P.IsClosed S :=
    g.range_isClosed
  have hPlusClosed : Plus.IsClosed S := by
    intro F xs U hxs hVal
    exact hOriginalClosed F.down xs U hxs hVal
  let TargetPlus : PartialSetStructure (L.withParts Parts) Y :=
    Target.withParts targetPart
  have hTrPlus : FibreTransversal TargetPlus targetPart :=
    (Target.withParts_fibreTransversal_iff targetPart).mpr hTr
  let jPlus : PartialSetStructure.Embedding
      (Plus.wholeWeakInduce S) TargetPlus :=
    wholeMaskCovered_closedExactTaggedTest_toPartialEmbedding
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover
      S hPlusClosed TargetPlus targetPart hTrPlus jTag
  have hSourceEq :
      (Plus.wholeWeakInduce S).originalLanguageReduct =
        P.wholeWeakInduce S := by
    rw [originalLanguageReduct_wholeWeakInduce]
    exact congrArg (fun A : PartialSetStructure L V => A.wholeWeakInduce S)
      (originalLanguageReduct_actualWholeMaskDecoder C)
  have hTargetEq :
      TargetPlus.originalLanguageReduct = Target :=
    originalLanguageReduct_withParts Target targetPart
  let jOriginal : PartialSetStructure.Embedding
      (P.wholeWeakInduce S) Target := by
    simpa only [hSourceEq, hTargetEq] using
      (jPlus.originalLanguageReduct)
  let gWeak : PartialSetStructure.Embedding
      E (P.wholeWeakInduce S) :=
    g.codRestrictWholeWeakRange
  let composite : PartialSetStructure.Embedding E Target :=
    jOriginal.comp gWeak
  refine ⟨composite, ?_⟩
  intro x
  rfl

end StructuralRamsey.RelStructure
