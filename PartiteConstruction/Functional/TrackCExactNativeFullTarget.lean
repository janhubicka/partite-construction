import PartiteConstruction.Functional.TrackCOptionFullExactRange
import PartiteConstruction.Functional.TrackCNativeFullPartialNoEmpty
import PartiteConstruction.Functional.TrackEClosedExactTaggedTestEmbedding2019
import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Track C: actual FULL native test E -> full genuine H partial target

This is the no-defined-empty subcase of the SAME-WITNESS protection
half of the English cover-and-pullback proof in Appendix A.

The original tagged 2019 C is a U-closed B-covered noncanonical
candidate. Its genuine partial decoder P can be noncanonical, but
suppose it has NoDefinedEmptyValues (as in the actual native B
two-pass witness). Let g:E -> P.collapseDomain be an ACTUAL full
native test copy, with exact image S=range(g).

If the exact induced OLD test C.induce S has a FULL embedding jTag
into the canonical tagged graph of an actual genuine partial
H-target, then the SAME vertex composite jTag ∘ g is a FULL
genuine Option(Set) embedding E.toNonemptyPartial -> Target.

Crucially:
* no generated closure hull replaces S, and its vertex budget does
  not change;
* the B-covered OLD candidate C is NOT assumed canonical;
* the target may contain defined-empty values; full Option maps
  reflect target domains on the tested copy;
* g need only be full on this E-test, not a globally injective EHN map.

The proof combines the verified exact closed tagged-test decoder
(Partite/Track E), the no-defined-empty full native->partial
map (#672), and the exact closed image factorization (#701).
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q Y T : Type v}

/-- The FULL actual native E-copy admits a FULL genuine partial
embedding into the SAME H-target, literally over jTag ∘ g on E.

The source target test S is precisely range(g). -/
noncomputable def wholeMaskCovered_exactNativeTest_toFullPartialTarget
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
    (hNoEmpty : NoDefinedEmptyValues (wholeMaskOriginalDecode C))
    (E : Structure L T)
    (g : Structure.Embedding E (wholeMaskOriginalDecode C).collapseDomain)
    (Target : PartialSetStructure L Y) [Finite Y]
    (targetPart : Y → Parts)
    (hTr : FibreTransversal Target targetPart)
    (jTag : Embedding (C.induce (Set.range g.toFun))
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart))) :
    ∃ k : PartialSetStructure.Embedding E.toNonemptyPartial Target,
      ∀ x : T,
        k.toFun x = jTag.toFun ⟨g.toFun x, ⟨x, rfl⟩⟩ := by
  classical
  let P : PartialSetStructure L V := wholeMaskOriginalDecode C
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let S : Set V := Set.range g.toFun
  have hOriginalClosed : P.IsClosed S :=
    (P.isClosed_iff_collapseDomain_isClosed S).mpr g.range_isClosed
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
  let gPartial : PartialSetStructure.Embedding E.toNonemptyPartial P :=
    g.toPartialOfNoDefinedEmpty hNoEmpty
  have hgToFun : gPartial.toFun = g.toFun := by
    funext x
    rfl
  have hRange : Set.range gPartial.toFun = S := by
    change Set.range gPartial.toFun = Set.range g.toFun
    rw [hgToFun]
  let gWeakRaw : PartialSetStructure.Embedding
      E.toNonemptyPartial
      (P.wholeWeakInduce (Set.range gPartial.toFun)) :=
    gPartial.codRestrictWholeWeakRange
  let gWeak : PartialSetStructure.Embedding
      E.toNonemptyPartial (P.wholeWeakInduce S) := by
    simpa only [hRange] using gWeakRaw
  let composite : PartialSetStructure.Embedding E.toNonemptyPartial Target :=
    jOriginal.comp gWeak
  refine ⟨composite, ?_⟩
  intro x
  rfl

end StructuralRamsey.RelStructure
