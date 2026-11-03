import PartiteConstruction.Functional.PartialWeakExactDomain2019
import PartiteConstruction.Functional.PartialWeakClosedAgreement2019
import PartiteConstruction.Structure.PartialSetFunctionsDomainGraph

/-!
# Track A — intrinsic partial domain graph versus ambient induced domain graph

The domain graph of a genuinely partial Option(Set) structure records
ordinary relations, definedness of each F (including some(∅)), and every
actual output incidence separately.

On the EXACT weak carrier S, **clipping preserves all output incidences**:
the output relation of (A.weakInduce S).domainGraph equals the induced
ambient output relation, with no closure or singleton assumption. But the
domain/root relation of the intrinsic clipped weak operation records only
defined-empty or surviving-output applications; it can lose a domain mask
which remains present in (A.domainGraph).induce S.

The complete ordinary/domain/output graph *does* commute with restriction
when S is function-closed, for both clipped and whole-fibre conventions.

In particular the 2019 OLD/U tagged construction must keep AMBIENT active
domain masks on arbitrary weak tests, not recompute them from intrinsic
weak operation domains. No tree or Ramsey hypothesis is used here.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every surviving output incidence of a clipped partial value is exactly
the corresponding ambient output incidence. This holds for arbitrary value
sets, including nullaries and all repeated input patterns. -/
theorem weakValue_hasOutput_iff
    (S : Set V) (value : Option (Set V)) (y : S) :
    (∃ T : Set S, weakValue S value = some T ∧ y ∈ T) ↔
      ∃ U : Set V, value = some U ∧ y.1 ∈ U := by
  classical
  cases value with
  | none =>
      simp [weakValue]
  | some U =>
      by_cases hU : U.Nonempty
      · by_cases hMeet : (U ∩ S).Nonempty
        · simp [weakValue, hU, hMeet]
        · have hNot : y.1 ∉ U := by
            intro hy
            exact hMeet ⟨y.1, hy, y.2⟩
          simp [weakValue, hU, hMeet, hNot]
      · have hNot : y.1 ∉ U := by
          intro hy
          exact hU ⟨y.1, hy⟩
        simp [weakValue, hU, hNot]

/-- The D(omain)-mask on a clipped weak test is precisely the surviving
domain; in particular a defined-empty value stays defined. -/
theorem weakInduce_domainGraph_domain_iff_exact
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (domainGraph (A.weakInduce S)).rel (.inr (.inl F)) xs ↔
      ∃ U : Set V, A.func F (Subtype.val ∘ xs) = some U ∧
        (U = ∅ ∨ (U ∩ S).Nonempty) := by
  exact weakInduce_defined_iff_exact A S F xs

/-- For whole-fibre restriction the intrinsic D-mask survives iff the
whole ambient output set survives. -/
theorem wholeWeakInduce_domainGraph_domain_iff_exact
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (domainGraph (A.wholeWeakInduce S)).rel (.inr (.inl F)) xs ↔
      ∃ U : Set V, A.func F (Subtype.val ∘ xs) = some U ∧
        U ⊆ S := by
  exact wholeWeakInduce_defined_iff_exact A S F xs

/-- Output relations, unlike domain relations, commute with arbitrary
CLIPPED weak restrictions, at precisely the same tested vertex set S. -/
theorem weakInduce_domainGraph_output_iff
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F + 1) → S) :
    (domainGraph (A.weakInduce S)).rel (.inr (.inr F)) xs ↔
      ((domainGraph A).induce S).rel (.inr (.inr F)) xs := by
  change
    (∃ T : Set S,
      weakValue S (A.func F
        (Subtype.val ∘ fun i => xs i.castSucc)) = some T ∧
      xs (Fin.last (L.funcArity F)) ∈ T) ↔
    (∃ U : Set V,
      A.func F (Subtype.val ∘ fun i => xs i.castSucc) = some U ∧
      (xs (Fin.last (L.funcArity F))).1 ∈ U)
  exact weakValue_hasOutput_iff S
    (A.func F (Subtype.val ∘ fun i => xs i.castSucc))
    (xs (Fin.last (L.funcArity F)))

/-- Every domain fact of an intrinsic clipped weak test comes from an
ambient domain fact; the converse fails when all outputs have escaped. -/
theorem weakInduce_domainGraph_domain_implies_ambient
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (domainGraph (A.weakInduce S)).rel (.inr (.inl F)) xs →
      ((domainGraph A).induce S).rel (.inr (.inl F)) xs := by
  exact weakInduce_defined_implies_ambient A S F xs

/-- Function-closedness repairs the domain mask discrepancy, including
defined-empty values and nullary roots. -/
theorem weakInduce_domainGraph_domain_iff_of_closed
    (A : PartialSetStructure L V) (S : Set V) (hS : A.IsClosed S)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (domainGraph (A.weakInduce S)).rel (.inr (.inl F)) xs ↔
      ((domainGraph A).induce S).rel (.inr (.inl F)) xs := by
  change (A.weakInduce S).Defined F xs ↔
    A.Defined F (Subtype.val ∘ xs)
  constructor
  · exact weakInduce_defined_implies_ambient A S F xs
  · rintro ⟨U, hU⟩
    have hUS : U ⊆ S :=
      hS F (Subtype.val ∘ xs) U (fun i => (xs i).2) hU
    refine ⟨{y : S | y.1 ∈ U}, ?_⟩
    change weakValue S (A.func F (Subtype.val ∘ xs)) =
      some {y : S | y.1 ∈ U}
    rw [hU]
    exact weakValue_of_subset S U hUS

/-- The whole two-relation partial function graph (including independent
domain masks) commutes with genuinely CLOSED weak restriction. -/
theorem weakInduce_domainGraph_rel_iff_of_closed
    (A : PartialSetStructure L V) (S : Set V) (hS : A.IsClosed S)
    (R : (domainGraphLanguage L).Symbol)
    (xs : Fin ((domainGraphLanguage L).arity R) → S) :
    (domainGraph (A.weakInduce S)).rel R xs ↔
      ((domainGraph A).induce S).rel R xs := by
  rcases R with R | R
  · rfl
  rcases R with F | F
  · exact weakInduce_domainGraph_domain_iff_of_closed A S hS F xs
  · exact weakInduce_domainGraph_output_iff A S F xs

/-- On closed S, whole-fibre restriction has the SAME full domain graph
as ordinary induced restriction of the ambient domain graph. -/
theorem wholeWeakInduce_domainGraph_rel_iff_of_closed
    (A : PartialSetStructure L V) (S : Set V) (hS : A.IsClosed S)
    (R : (domainGraphLanguage L).Symbol)
    (xs : Fin ((domainGraphLanguage L).arity R) → S) :
    (domainGraph (A.wholeWeakInduce S)).rel R xs ↔
      ((domainGraph A).induce S).rel R xs := by
  rw [← weakInduce_eq_wholeWeakInduce_of_closed A S hS]
  exact weakInduce_domainGraph_rel_iff_of_closed A S hS R xs

end StructuralRamsey.PartialSetStructure
