import PartiteConstruction.Functional.TrackCRichActualTaggedUIrred2019
import PartiteConstruction.Functional.TrackCRichExactImageIrreducible
import PartiteConstruction.Functional.TrackCRichOriginalReductIrreducible
import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019

/-!
# Track C: actual full rich E-copy gives EXACT intrinsically U-irreducible OLD test

This is the first-stage same-map protection geometry missing from the
genuinely rich Option(Set) Appendix A cover-and-pullback argument.

Let C be the ACTUAL noncanonical U-closed B-covered OLD tagged witness
in the language with unary part predicates. Its ORIGINAL unlabelled
Option(Set) decoder P retains undefined vs some(empty).

For a FULL original genuine partial embedding e:E↪P with E
domain-aware closed-free-irreducible, define S=range(e) exactly.
A full embedding has function-closed image S. The verified #701
exact-image factor and the generic rich isomorphism-invariance
lemma show that P.wholeWeakInduce S is still irreducible.
The exact originalLanguageReduct dictionary and the forget-parts
irreducibility lemma pass this to the actual PART-LABELLED
partial decoder on the SAME S.

The actual tagged U-irreducibility theorem then gives
IsUIrreducible C.induce(S). In particular a selected protected OLD
completion of C.induce(q[T]) is FULL on every q[E]⊆q[T],
on the SAME vertex map and with no closure-hull growth.

This is not a global HE upgrade, not the existence of the selected
H-completion f_S, and not the final intrinsic class Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q T : Type v}

/-- Every full genuine Option(Set) irreducible E-copy in the ORIGINAL
decoder of the ACTUAL covered 2019 final tagged C has an exact
tagged U-irreducible vertex image. The source may have defined-empty
inputs, the actual OLD C need not be canonical, and S is literal
range(e) with no additional vertices. -/
theorem wholeMaskCovered_exactRichIrredCopy_taggedUIrreducible
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (E : PartialSetStructure L T)
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : PartialSetStructure.Embedding E (wholeMaskOriginalDecode C)) :
    IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (Set.range e.toFun)) := by
  classical
  let P0 : PartialSetStructure L V := wholeMaskOriginalDecode C
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let S : Set V := Set.range e.toFun
  have hOriginalClosed : P0.IsClosed S := e.range_isClosed
  have hPlusClosed : Plus.IsClosed S := by
    intro F xs U hxs hVal
    exact hOriginalClosed F.down xs U hxs hVal
  have hOriginalImageIrred :
      (P0.wholeWeakInduce S).IsOptionClosedFreeIrreducible :=
    hE.exactWholeWeakRange e
  have hOriginalWeakEq :
      (Plus.wholeWeakInduce S).originalLanguageReduct =
        P0.wholeWeakInduce S := by
    rw [originalLanguageReduct_wholeWeakInduce]
    exact congrArg (fun A : PartialSetStructure L V => A.wholeWeakInduce S)
      (originalLanguageReduct_actualWholeMaskDecoder C)
  have hPlusOriginalIrred :
      (Plus.wholeWeakInduce S).originalLanguageReduct
        .IsOptionClosedFreeIrreducible := by
    simpa only [hOriginalWeakEq] using hOriginalImageIrred
  have hPlusIrred :
      (Plus.wholeWeakInduce S).IsOptionClosedFreeIrreducible :=
    IsOptionClosedFreeIrreducible.of_originalLanguageReduct
      (Plus.wholeWeakInduce S) hPlusOriginalIrred
  exact wholeMaskCovered_inducedUIrreducible_of_richOptionIrreducible
    C (Base.withParts basePart) basePart
    hC (hPos.withParts) hCover
    S hPlusClosed hPlusIrred

end StructuralRamsey.RelStructure
