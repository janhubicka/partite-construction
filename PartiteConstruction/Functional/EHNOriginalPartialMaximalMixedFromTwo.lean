import PartiteConstruction.Functional.EHNOriginalPartialStrictIteratedRank
import PartiteConstruction.Functional.EHNNativeOriginalPartialRankOne

/-!
# The remaining strict functional mixed-root schema starts at rank TWO

The completed n-pass original-partial strict-tree theorem in the native
functional EHN library exposes a uniform maximal-mixed-root relative
extension schema as its only unproved mathematical hypothesis.

The first rank is NOW verified unconditionally, and the general
one-generator full free-amalgam localization is completely independent
of function arity and of the partite projection. Therefore the schema
is already automatic at rank 0 and 1 for EVERY actual native
attachment: any generated test is contained in a constituent side,
so it cannot satisfy both mixed-exterior hypotheses.

This file proves that the full uniform schema is logically equivalent
to its restriction to ranks >=2, and restates the complete native n-pass
and final B-cover theorem using ONLY that sharper unresolved premise.
The proof merely invokes already checked rank-one geometry and the
already checked conditional full n-pass theorem; it does not redo
induced or recursive Ramsey constructions.

This is still conditional for rank >=2. No compatible maximal mixed-root
extension is asserted without proof.
-/

namespace StructuralRamsey.FunctionalPartite.EHN.StrictRanked

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Uniform maximal mixed-root extension requests ONLY at generator
ranks n >= 2. This is the genuine outstanding part of the functional
2019 partial-map strict-tree sparsening argument. -/
def MaximalMixedSchemaFromTwo
    (K : Structure.StructureClass (L := L))
    (A : Structure L U) (Base : Structure L V) : Prop :=
  ∀ (Q : Type v) [Finite Q] [DecidableEq Q]
    (Control : Structure L Q) (n : ℕ),
    2 ≤ n →
    ∀ (Old T : EHN.Stage K Control)
      (alpha : Structure.Embedding A Control)
      (f : FunctionalPartite.Embedding
        (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed
            Control Old.isPartite.1 A alpha))
        T.system),
      LocallyGeneratedOriginalPartialTreeCompletable
        Base Old.system.toStructure n →
      LocallyGeneratedOriginalPartialTreeCompletable
        Base T.system.toStructure n →
      Attachment.NativeMaximalMixedOriginalPartialRelativeExtension
        Old.system (Old.system.support alpha.toFunctionEmbedding)
        (Old.system.weak_support_closed
          Control Old.isPartite.1 A alpha)
        T.system f Base n

/-- With n <= 1, every actual native maximal mixed-root completion
request is contradictory: its exact closed test is one-generated,
hence lies wholly in either the core or one copied old stage.
The projected-image equality hypothesis is not even needed. -/
theorem maximalMixed_rank_le_one_vacuous
    {P W X VB : Type v}
    (B : FunctionalPartite.System L P W)
    (S : Set W) (hS : B.toStructure.IsClosed S)
    (D : FunctionalPartite.System L P X)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Base : Structure L VB) [DecidableEq P]
    (n : ℕ) (hn : n ≤ 1) :
    Attachment.NativeMaximalMixedOriginalPartialRelativeExtension
      B S hS D f Base n := by
  intro Test hTest G hGen hCard _hImage hNotCore hNotCopy
  have hOne : ((Attachment.UnitAttachD B S hS D f).toStructure.induce
      Test hTest).GeneratedByAtMost 1 :=
    ⟨G, hCard.trans hn, hGen⟩
  rcases Attachment.nativeClosedTest_rankOne_pure
      B S hS D f Test hTest hOne with hCore | hCopy
  · exact (hNotCore hCore).elim
  · exact (hNotCopy hCopy).elim

/-- The full uniform schema follows from its rank >=2 restriction.
Ranks 0 and 1 are supplied by exact full-functional free-amalgam
geometry rather than being assumed or postulated. -/
theorem MaximalMixedSchema.of_from_two
    {K : Structure.StructureClass (L := L)}
    {A : Structure L U} {Base : Structure L V}
    (h : MaximalMixedSchemaFromTwo K A Base) :
    MaximalMixedSchema K A Base := by
  intro Q _ _ Control n Old T alpha f hOld hCore
  by_cases hn : n ≤ 1
  · exact maximalMixed_rank_le_one_vacuous
      Old.system (Old.system.support alpha.toFunctionEmbedding)
      (Old.system.weak_support_closed
        Control Old.isPartite.1 A alpha)
      T.system f Base n hn
  · have h2 : 2 ≤ n := by omega
    exact h Q Control n h2 Old T alpha f hOld hCore

/-- The converse is restriction of the fully quantified schema. -/
theorem MaximalMixedSchema.to_from_two
    {K : Structure.StructureClass (L := L)}
    {A : Structure L U} {Base : Structure L V}
    (h : MaximalMixedSchema K A Base) :
    MaximalMixedSchemaFromTwo K A Base := by
  intro Q _ _ Control n h2 Old T alpha f hOld hCore
  exact h Q Control n Old T alpha f hOld hCore

/-- Verified complete n-pass strict functional sparsening with the
strongest CURRENTLY justified hypothesis: compatible maximal-mixed
relative B-tree extensions only for ranks >=2. Ranks 0 and 1, all
Ramsey canonicalization, all pure/small-image cases, the original
partial projection and the final B-coverage are already checked. -/
theorem sparsening_of_maximal_mixed_schema_from_two
    {P : Type v}
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hMixed : MaximalMixedSchemaFromTwo K A Base)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A Base C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      LocallyClosedOriginalPartialTreeCompletable Base C n ∧
      IrreduciblesExtendTo Base C ∧
      LooseTreeAmalgam Base W C := by
  exact sparsening_of_maximal_mixed_schema
    K hK A Base D hKA hKB hBIrr hPos eAB
    κ hArrow (MaximalMixedSchema.of_from_two hMixed) n hn

end StructuralRamsey.FunctionalPartite.EHN.StrictRanked
