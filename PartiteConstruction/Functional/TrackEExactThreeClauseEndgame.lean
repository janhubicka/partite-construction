import PartiteConstruction.Functional.TrackEStatementAudit
import PartiteConstruction.Functional.PublishedSparseningLoose

/-!
# Appendix A Track E: exact three-clause endgame with one common C and p

The historical full-functional three-clause target is equivalent, on one
literal Ramsey witness C and one literal global map p, to the corrected
2019 source-defined global homomorphism-embedding, **plus** domain
reflection at ALL function inputs, **plus** STRICT genuine functional
B-tree completability at the printed cutoff n, **plus** internal
irreducible B-extension.

This is an exact logical comparison, NOT a new existence theorem for
the conditions on the right. In the finite binary counterexample, domain
reflection is impossible for *every* corrected witness carrying the
Ramsey arrow and internal B-copy extension, independently of the
unproved strict B-tree completion.

The result below also proves the obstruction is NONVACUOUS for an actual
output of the separately verified native EHN + loose-tree construction.
There is no new axiom, no assumption of the false maximal mixed-root
schema, and no alteration of the exact tested S.
-/

namespace StructuralRamsey.Structure.TrackEExactThreeClauseEndgame

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackEStatementAudit

universe u v

variable {L : Language.{u}} {U V P : Type v}

/-- Corrected strict functional sparsening on ONE witness and ONE
original-2019 projection, with the EXACT missing domain-reflection
hypothesis exposed rather than silently asserted. -/
def SourceDefinedStrictAndDomainReflectingConclusion
    (A : Structure L U) (Base : Structure L V)
    (D : Structure L P) (κ : Type*) (n : ℕ) : Prop :=
  ∃ (X : Type v) (_ : Finite X) (C : Structure L X) (p : X → P),
    Arrow A Base C κ ∧
    IsOriginalPartialHomomorphismEmbedding C D p ∧
    (∀ F (x : Fin (L.funcArity F) → X),
      (D.func F (p ∘ x)).Nonempty → (C.func F x).Nonempty) ∧
    LocallyClosedTreeCompletable Base C n ∧
    IrreduciblesExtendTo Base C

/-- EXACT iff with the literal historical three clauses; no witness
change, no local size/rank change, no distinct projection map, and
no replacement of strict B-trees by graph or loose trees. -/
theorem historicalThreeClauses_iff_sourceDefinedStrictReflected
    (A : Structure L U) (Base : Structure L V)
    (D : Structure L P) (κ : Type*) (n : ℕ) :
    PublishedSparseningConclusion A Base D κ n ↔
    SourceDefinedStrictAndDomainReflectingConclusion A Base D κ n := by
  constructor
  · rintro ⟨X, hX, C, hArrow, p, hFull, hLocal, hCover⟩
    refine ⟨X, hX, C, p, hArrow, ?_, ?_, hLocal, hCover⟩
    · exact totalHE_implies_originalPartialHE hFull
    · exact (totalHE_iff_originalPartialHE_and_domainReflection.mp hFull).2
  · rintro ⟨X, hX, C, p, hArrow, hPartial, hReflect, hLocal, hCover⟩
    refine ⟨X, hX, C, hArrow, p, ?_, hLocal, hCover⟩
    exact (totalHE_iff_originalPartialHE_and_domainReflection).mpr
      ⟨hPartial, hReflect⟩

/-- A certified finite binary-function Ramsey and B-covered C that
projects in the genuine 2019 partial sense to the three-point
left-projection D MUST have an undefined source input whose image
is defined in D. We do not require any local B-tree hypothesis;
the obstruction is already forced by Ramsey+internal B coverage. -/
theorem unavoidable_domain_loss_for_corrected_Bcover
    {X : Type}
    (C : Structure PublishedTotalBinaryObstruction.language X)
    (hArrow : Arrow PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B C (Fin 2))
    (p : X → Fin 3)
    (hPartial : IsOriginalPartialHomomorphismEmbedding
      C PublishedTotalBinaryObstruction.D p)
    (hCover : IrreduciblesExtendTo PublishedTotalBinaryObstruction.B C) :
    ∃ (F : PublishedTotalBinaryObstruction.language.FuncSymbol)
      (x : Fin (PublishedTotalBinaryObstruction.language.funcArity F) → X),
      (PublishedTotalBinaryObstruction.D.func F (p ∘ x)).Nonempty ∧
      ¬ (C.func F x).Nonempty := by
  classical
  by_contra hNone
  have hReflect : ∀ F (x : Fin
      (PublishedTotalBinaryObstruction.language.funcArity F) → X),
      (PublishedTotalBinaryObstruction.D.func F (p ∘ x)).Nonempty →
      (C.func F x).Nonempty := by
    intro F x htgt
    by_contra hsrc
    exact hNone ⟨F, x, htgt, hsrc⟩
  have hFull : C.IsHomomorphism PublishedTotalBinaryObstruction.D p :=
    hPartial.toEHN.isHomomorphism_of_domainReflection hReflect
  exact PublishedTotalBinaryObstruction.no_full_projection_and_irreducible_extension
    C hArrow p hFull hCover

/-- The missing-domain obstruction is REALIZED on an actual FINITE
corrected Ramsey witness from the verified all-arity full-function
EHN + loose B-tree construction, not merely a formal implication
whose corrected hypotheses might be inconsistent.

The strict genuine functional tree is NOT asserted: the actual C
is a LOOSE full-functional B-tree with internal B extension. -/
theorem actual_corrected_Bcovered_RamseyWitness_loses_domain :
    ∃ (X : Type) (_ : Finite X)
      (C : Structure PublishedTotalBinaryObstruction.language X),
      Arrow PublishedTotalBinaryObstruction.A
        PublishedTotalBinaryObstruction.B C (Fin 2) ∧
      IrreduciblesExtendTo PublishedTotalBinaryObstruction.B C ∧
      LooseTreeAmalgam PublishedTotalBinaryObstruction.B X C ∧
      ∃ p : X → Fin 3,
        IsOriginalPartialHomomorphismEmbedding
          C PublishedTotalBinaryObstruction.D p ∧
        ∃ (F : PublishedTotalBinaryObstruction.language.FuncSymbol)
          (x : Fin (PublishedTotalBinaryObstruction.language.funcArity F) → X),
          (PublishedTotalBinaryObstruction.D.func F (p ∘ x)).Nonempty ∧
          ¬ (C.func F x).Nonempty := by
  obtain ⟨X, hX, C, hArrow, ⟨p, hp⟩, hLoose, hCover, _hLocal⟩ :=
    sparseningRamsey_functional_looseFullTrees
      PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.D
      (Fin 2)
      PublishedTotalBinaryObstruction.three_ramsey_two
  exact ⟨X, hX, C, hArrow, hCover, hLoose,
    p, hp.toOriginalPartial,
    unavoidable_domain_loss_for_corrected_Bcover C hArrow p
      hp.toOriginalPartial hCover⟩

/-- The historic full three-clause target cannot be recovered by merely
requiring its missing two conditions: in the checked binary example,
the exact whole package is impossible at EVERY finite cutoff n. -/
theorem no_strictAndReflected_candidate_for_binary_Ramsey (n : ℕ) :
    ¬ SourceDefinedStrictAndDomainReflectingConclusion
      PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.D (Fin 2) n := by
  intro h
  exact PublishedTotalBinaryObstruction.not_publishedSparseningConclusion_all n
    ((historicalThreeClauses_iff_sourceDefinedStrictReflected
      PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.D (Fin 2) n).mpr h)

end StructuralRamsey.Structure.TrackEExactThreeClauseEndgame
