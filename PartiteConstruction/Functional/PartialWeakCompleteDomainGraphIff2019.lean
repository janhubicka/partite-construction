import PartiteConstruction.Functional.PartialWeakAmbientDomainGraph2019
import PartiteConstruction.Functional.PartialWeakDomainAgreementCriteria2019

/-!
# Track A: complete exact ambient/intrinsic partial-domain-graph equivalences

The previous two merged modules proved, separately, that output incidence
commutes with *clipped* weak restriction, and gave the sharp agreement criteria
for the domain bit. This module assembles these into exact conditions for the
ENTIRE relationalized partial-function structure on the unchanged carrier S.

Clipping: ambient induced domainGraph = graph of intrinsic weakInduce
if and only if no defined nonempty fibre loses every output.

Whole-fibre deletion: the two entire graphs agree if and only if S is
genuinely function-closed.

The converse to the latter is not a consequence of part saturation or output
transversality: the two-output transversal cut established in Track A has
no lost clipped applications, yet is not function-closed.

Neither statement identifies the ambient OLD U-closed encoding with an
arbitrary intrinsic weak test without its required domain-mask hypothesis.
All arities (including nullary), defined-empty values, and repeated inputs
are handled by the underlying exact-domain lemmas.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Exact criterion for equality of ALL ordinary relations, independently
recorded domain predicates and positive output incidences between the
intrinsic clipped weak graph and induced AMBIENT domain graph. -/
theorem clippedDomainGraph_agrees_iff_noLost
    (A : PartialSetStructure L V) (S : Set V) :
    (∀ (R : (domainGraphLanguage L).Symbol)
        (xs : Fin ((domainGraphLanguage L).arity R) → S),
      (domainGraph (A.weakInduce S)).rel R xs ↔
      ((domainGraph A).induce S).rel R xs) ↔
      NoLostDefinedApplications A S := by
  constructor
  · intro h
    apply (weakDomain_agrees_iff_noLost A S).mp
    intro F xs
    exact h (.inr (.inl F)) xs
  · intro hNo R xs
    rcases R with R | R
    · rfl
    rcases R with F | F
    · exact ((weakDomain_agrees_iff_noLost A S).mpr hNo) F xs
    · exact weakInduce_domainGraph_output_iff A S F xs

/-- Whole-fibre deletion matches the COMPLETE AMBIENT induced domain graph
on the exact carrier S precisely for genuinely function-closed S. -/
theorem wholeDomainGraph_agrees_iff_closed
    (A : PartialSetStructure L V) (S : Set V) :
    (∀ (R : (domainGraphLanguage L).Symbol)
        (xs : Fin ((domainGraphLanguage L).arity R) → S),
      (domainGraph (A.wholeWeakInduce S)).rel R xs ↔
      ((domainGraph A).induce S).rel R xs) ↔
      A.IsClosed S := by
  constructor
  · intro h
    apply (wholeDomain_agrees_iff_closed A S).mp
    intro F xs
    exact h (.inr (.inl F)) xs
  · intro hClosed R xs
    exact wholeWeakInduce_domainGraph_rel_iff_of_closed
      A S hClosed R xs

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.TrackASaturation

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

/-- A genuine transversal and part-saturated but NONCLOSED test can have
the entire clipped domain graph agree with induced ambient relations,
while the entire whole-fibre graph still fails to agree. This witnesses
strictness of the two conditions, not an obstruction to the corrected
relative OLD-encoding invariant. -/
theorem clippedGraph_agrees_but_wholeGraph_does_not :
    (∀ (R : (domainGraphLanguage language).Symbol)
        (xs : Fin ((domainGraphLanguage language).arity R) → S),
      (domainGraph (examplePartial.weakInduce S)).rel R xs ↔
      ((domainGraph examplePartial).induce S).rel R xs) ∧
    ¬ (∀ (R : (domainGraphLanguage language).Symbol)
        (xs : Fin ((domainGraphLanguage language).arity R) → S),
      (domainGraph (examplePartial.wholeWeakInduce S)).rel R xs ↔
      ((domainGraph examplePartial).induce S).rel R xs) := by
  obtain ⟨hNo, hNotClosed⟩ := noLost_even_though_not_closed
  constructor
  · exact (clippedDomainGraph_agrees_iff_noLost
      examplePartial S).mpr hNo
  · intro h
    exact hNotClosed ((wholeDomainGraph_agrees_iff_closed
      examplePartial S).mp h)

end StructuralRamsey.FunctionalPartite.TrackASaturation
