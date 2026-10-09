import PartiteConstruction.Ramsey.ClosurePowerOneProtected

/-! # Conditional complete local Ramsey/protected Picture step

The finite native Hales--Jewett partite lemma is already formalized. Once
the protected part projection of every positive coordinate power of the
restricted old system is available, the *actual* all-embeddings Picture
witness is finite, closed, projects by a protected map to the original
part structure, and covers all protected tests by B-copies.

The higher-power projection premise is deliberately NOT replaced with
ordinary partiteness, nor treated as an axiom. This theorem isolates
precisely what remains to make the local Ramsey step fully protected.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v}

/-- The local Hales--Jewett Picture preserves the entire working
completion invariant whenever positive powers preserve the same
protected projection. Only the latter is a remaining hypothesis. -/
theorem pictureLemma_protected_of_power
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure D B.part)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite Q] [Finite V]
    (Color : Type*) [Fintype Color]
    (hPower : ∀ N : ℕ, 0 < N →
      IsClosedUHomomorphismEmbedding rules
        (power (B.restrict alpha.toFunctionEmbedding) N).toRelStructure
        A (power (B.restrict alpha.toFunctionEmbedding) N).part) :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      PictureProperty A B alpha.toFunctionEmbedding C Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  classical
  let af := alpha.toFunctionEmbedding
  let R := B.restrict af
  have hOldOrdinary : B.IsPartiteOver D :=
    hBPart.toHomomorphismEmbedding_of_closed hB
  have hRPart : R.IsPartiteOver A :=
    restrict_isPartiteOver D B A hOldOrdinary alpha
  obtain ⟨N, hN, hArrow⟩ :=
    partiteLemma (A := A) (B := R) hRPart Color
  let E := power R N
  have hSupport : IsUSubstructure rules
      B.toRelStructure (B.support af) :=
    support_isUSubstructure_of_closed_part_copy
      A D B alpha hA hD hOldOrdinary
  have hRClosed : IsUClosed rules R.toRelStructure :=
    hB.induce_of_USubstructure (B.support af) hSupport
  have hEClosed : IsUClosed rules E.toRelStructure :=
    power_isUClosed R hRPart hA hRClosed hN
  have hEPart : IsClosedUHomomorphismEmbedding rules
      E.toRelStructure A E.part := hPower N hN
  obtain ⟨hWhole, hProjection, hCoverage⟩ :=
    picture_build_protected_step A D B alpha E hA hD hB
      hEClosed hBPart hEPart aB
  exact ⟨Picture.Vertex B af E, inferInstance,
    Picture.build B af E,
    Picture.property B af E Color hArrow,
    hWhole, hProjection, hCoverage⟩

end StructuralRamsey.Partite.Induced
