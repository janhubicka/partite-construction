import PartiteConstruction.Functional.TrackCRichDefinedRootSide2019
import PartiteConstruction.Functional.TrackCOptionIrredNative
import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019
import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-!
# Track C: exact rich partial irreducible image is U-irreducible in actual OLD

On the actual U-closed canonical-B-covered final 2019 tagged source
C, with its noncanonical genuine Option(Set) decoder A, fix an EXACT
vertex set S which is function-closed in A.

If the GENUINE whole-fibre weak restriction A.wholeWeakInduce S is
irreducible for domain-aware closed free covers, then the actual OLD
tagged test C.induce S is intrinsically U-irreducible.

Unlike the existing native-collapse version, this recognizes the
active mixed defined-empty function input (which has no outputs).
It uses the ACTUAL final OLD source C; no equality with a canonical
tag expansion, closure-hull replacement, or new vertices is assumed.

The proof combines already checked relative U-closed -> function-closed
side transport, literal original-relation localization, and the
new complete-OLD-input-root lemma for ALL defined values (including
some empty). It does not assume global tagged control-map fullness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- The original true Option(Set) closed-free irreducibility of an
EXACT closed weak test of the actual final 2019 decoder suffices to
make the corresponding ACTUAL tagged induced test U-irreducible.
All source-defined-empty input tuples remain active, and the
irreducibility is not tested after collapseDomain. -/
theorem wholeMaskCovered_inducedUIrreducible_of_richOptionIrreducible
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) Z),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (hRichIrred :
      ((wholeMaskTagReduct C).wholeMaskPartialDecode.wholeWeakInduce S)
        .IsOptionClosedFreeIrreducible) :
    IsUIrreducible (L.wholeMaskClosureRules P) (C.induce S) := by
  classical
  let A : PartialSetStructure L V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  have hCU : IsUClosed (L.wholeMaskClosureRules P)
      (C.induce S) :=
    (wholeMaskCovered_inducedUClosed_iff_decodedClosed
      C Base part hC hPos hCover S).mpr hS
  apply hCU.uIrreducible_of_closed_cover
  intro X Y hX hY hCovered hTuples
  have hClosedSide
      (Side : Set S)
      (hSide : IsUSubstructure (L.wholeMaskClosureRules P)
        (C.induce S) Side) :
      (A.wholeWeakInduce S).IsClosed Side := by
    have hNative :
        (A.collapseDomain.induce S
          ((A.isClosed_iff_collapseDomain_isClosed S).mp hS))
          .IsClosed Side :=
      wholeMaskCovered_inducedUSubstructure_to_nativeClosed
        C Base part hC hPos hCover S hS Side hSide
    apply (A.wholeWeakInduce S).isClosed_iff_collapseDomain_isClosed Side |>.mpr
    rw [wholeWeakInduce_collapse_eq_nativeInduce A S hS]
    exact hNative
  have hRelations :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → S),
        (A.wholeWeakInduce S).rel R xs →
        (∀ i, xs i ∈ X) ∨ (∀ i, xs i ∈ Y) := by
    intro R xs hRel
    have hOld : (C.induce S).rel (.inl (.inl R)) xs := hRel
    exact hTuples (.inl (.inl R)) xs hOld
  have hDefined :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
        (U : Set S),
        (A.wholeWeakInduce S).func F xs = some U →
        (∀ i, xs i ∈ X) ∨ (∀ i, xs i ∈ Y) := by
    intro F xs U hSome
    exact wholeMaskCovered_inducedWholeWeakDefinedInput_side
      C Base part hC hPos hCover S hS X Y hTuples F xs U hSome
  exact hRichIrred X Y
    (hClosedSide X hX) (hClosedSide Y hY)
    hCovered hRelations hDefined

end StructuralRamsey.RelStructure
