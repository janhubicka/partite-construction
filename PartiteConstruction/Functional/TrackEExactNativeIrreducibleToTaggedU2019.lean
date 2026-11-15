import PartiteConstruction.Functional.TrackENativeClosedCoverIrreducibility2019
import PartiteConstruction.Functional.TrackEFinalInducedTestLocalization2019
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-!
# Track E: exact native closed irreducible test is intrinsically tagged U-irreducible

For the ACTUAL U-closed and protected noncanonical whole-mask tagged
target C, a native function-closed exact S with irreducible induced
full-functional decoder N|S gives a U-closed/U-irreducible tagged C|S.
The proof transfers a hypothetical relative tagged U-free cover to a
literal native closed free cover, using complete OLD value tuples
to prevent crossing native function incidences. No S→closure(S).
This is a conditional source semantic theorem, not a claimed global
HE to the selected control and not a native strict B-tree completion.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V X : Type v}

/-- Every full native irreducible exact CLOSED test of the covered
whole-mask decoder is a tagged U-irreducible test on LITERALLY S. -/
theorem wholeMaskCovered_exactNativeIrred_to_closedTaggedUIrred
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L X)
    (basePart : X → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (S : Set V)
    (hS : (wholeMaskOriginalDecode C).collapseDomain.IsClosed S)
    (hIrred :
      (((wholeMaskOriginalDecode C).collapseDomain).induce S hS).Irreducible) :
    IsUClosed ((L.withParts P).wholeMaskClosureRules P) (C.induce S) ∧
    IsUIrreducible ((L.withParts P).wholeMaskClosureRules P)
      (C.induce S) := by
  classical
  let A : PartialSetStructure (L.withParts P) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let N : Structure L V := (wholeMaskOriginalDecode C).collapseDomain
  have hOriginalPartial : (wholeMaskOriginalDecode C).IsClosed S :=
    (PartialSetStructure.isClosed_iff_collapseDomain_isClosed
      (wholeMaskOriginalDecode C) S).mpr hS
  have hFullPartial : A.IsClosed S := by
    intro F xs U hxs hValue
    cases F with
    | up F =>
        exact hOriginalPartial F xs U hxs hValue
  have hFullNative : A.collapseDomain.IsClosed S :=
    (PartialSetStructure.isClosed_iff_collapseDomain_isClosed A S).mp
      hFullPartial
  have hClosed :
      IsUClosed ((L.withParts P).wholeMaskClosureRules P)
        (C.induce S) :=
    (wholeMaskCovered_inducedUClosed_iff_decodedClosed
      C (Base.withParts basePart) basePart hC
      hPos.withParts hCover S).mpr hFullPartial
  refine ⟨hClosed, ?_⟩
  apply hClosed.uIrreducible_of_closed_cover
  intro SideL SideR hRelL hRelR hAll hTuples
  have hLeftFull :
      (A.collapseDomain.induce S hFullNative).IsClosed SideL :=
    wholeMaskCovered_inducedUSubstructure_to_nativeClosed
      C (Base.withParts basePart) basePart hC
      hPos.withParts hCover S hFullPartial SideL hRelL
  have hRightFull :
      (A.collapseDomain.induce S hFullNative).IsClosed SideR :=
    wholeMaskCovered_inducedUSubstructure_to_nativeClosed
      C (Base.withParts basePart) basePart hC
      hPos.withParts hCover S hFullPartial SideR hRelR
  have hLeft :
      (N.induce S hS).IsClosed SideL := by
    intro F xs hArgs y hy
    exact hLeftFull (ULift.up F) xs hArgs hy
  have hRight :
      (N.induce S hS).IsClosed SideR := by
    intro F xs hArgs y hy
    exact hRightFull (ULift.up F) xs hArgs hy
  have hRel :
      ∀ R (t : Fin (L.relArity R) → S),
        (N.induce S hS).rel R t →
          (∀ k, t k ∈ SideL) ∨ (∀ k, t k ∈ SideR) := by
    intro R t ht
    exact hTuples (.inl (.inl (.inl (ULift.up R)))) t ht
  have hFunc :
      ∀ F (xs : Fin (L.funcArity F) → S) (y : S),
        y ∈ (N.induce S hS).func F xs →
          ((∀ i, xs i ∈ SideL) ∧ y ∈ SideL) ∨
          ((∀ i, xs i ∈ SideR) ∧ y ∈ SideR) := by
    intro F xs y hy
    have hyFull :
        y ∈ (A.collapseDomain.induce S hFullNative).func
          (ULift.up F) xs := hy
    exact wholeMaskCovered_inducedNativeFunctionIncident_side
      C (Base.withParts basePart) basePart hC
      hPos.withParts hCover S hFullPartial
      SideL SideR hTuples (ULift.up F) xs y hyFull
  exact Structure.Irreducible.closed_cover_of_local_incidents
    (N.induce S hS) hIrred
    SideL SideR hLeft hRight hAll hRel hFunc

end StructuralRamsey.RelStructure
