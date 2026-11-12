import PartiteConstruction.Functional.PartialWeakExactInclusionCriteria2019
import PartiteConstruction.Functional.PartialWeakClippingWholeSingletonDictionary2019
import PartiteConstruction.Functional.WholeMaskWeakDomainUnaryExample2019

/-!
# Track A — the exact semantic square for clipped weak inclusions

Let A have genuine partial set-valued operations, and take the CLIPPED weak
restriction on an arbitrary exact vertex set S. Three different notions of
mapping this weak test into A must not be conflated:

* the independent Dom_F / Graph_F representation always has a POSITIVE
  relational homomorphism on the literal inclusion map;
* it has an INDUCED relational embedding iff no ambient defined input
  loses every output (NoLostDefinedApplications);
* the literal inclusion is an ORIGINAL source-defined partial-functional
  homomorphism iff no ambient output fibre is partially retained across S
  (NoPartiallyRetainedValues).

These last two sharp criteria are independent: one is about losing ALL
outputs, the other about losing SOME outputs. Their CONJUNCTION is
equivalent to actual function-closedness of S, and thus to the literal
inclusion being a FULL functional embedding.

All claims use exactly S, not its closure hull. Defined-empty `some ∅`,
undefined `none`, nullaries, repeated inputs, and multi-output fibres
are handled in the general statements. The purely source-semantic square
neither proves the ambient relative local-class implication nor the strict
history-compatible B-tree completion.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every clipped weak test has a POSITIVE relational domain/output graph
map to the ambient structure. It need not be an induced graph embedding,
as complete loss of an output can erase an intrinsic domain bit. -/
theorem clippedWeakGraphInclusion_positive
    (A : PartialSetStructure L V) (S : Set V) :
    (domainGraph (A.weakInduce S)).IsHomomorphism
      (domainGraph A) (Subtype.val : S → V) := by
  intro symbol xs h
  cases symbol with
  | inl R =>
      exact h
  | inr symbol =>
      cases symbol with
      | inl F =>
          exact weakInduce_domainGraph_domain_implies_ambient A S F xs h
      | inr F =>
          exact (weakInduce_domainGraph_output_iff A S F xs).mp h

/-- Sharp criterion for when the SAME clipped weak inclusion is a
SOURCE-DEFINED partial-function homomorphism. This is not the induced
domain-graph criterion: a surviving partially clipped multivalued
output fails onto-fibre preservation, while a completely lost output
does not constrain a source-undefined application. -/
theorem clippedWeakInclusion_originalPartial_iff_noPartial
    (A : PartialSetStructure L V) (S : Set V) :
    IsOriginalPartialHomomorphism (A.weakInduce S) A
      (Subtype.val : S → V) ↔
      NoPartiallyRetainedValues A S := by
  constructor
  · intro h F xs U hVal
    by_cases hSub : U ⊆ S
    · exact Or.inl hSub
    · right
      intro hMeet
      have hUNonempty : U.Nonempty := by
        obtain ⟨y, hy, _⟩ := hMeet
        exact ⟨y, hy⟩
      have hWeak : (A.weakInduce S).func F xs =
          some {y : S | y.1 ∈ U} := by
        change weakValue S (A.func F (Subtype.val ∘ xs)) =
          some {y : S | y.1 ∈ U}
        rw [hVal]
        simp [weakValue, hUNonempty, hMeet]
      have hEq := h.2 F xs {y : S | y.1 ∈ U} hWeak
      rw [hVal] at hEq
      have hUeq : U = Structure.imageSet Subtype.val
          ({y : S | y.1 ∈ U}) :=
        Option.some.inj hEq
      apply hSub
      intro y hy
      rw [hUeq] at hy
      obtain ⟨z, _hz, rfl⟩ := hy
      exact z.2
  · intro hNo
    rw [weakInduce_eq_wholeWeakInduce_of_noPartial A S hNo]
    exact wholeWeakInclusion_originalPartial A S

/-- No defined input loses ALL outputs AND no surviving fibre is only
PARTIALLY retained iff the exact tested carrier S is function-closed.
The two independent weaknesses repair each other. -/
theorem noLost_and_noPartial_iff_closed
    (A : PartialSetStructure L V) (S : Set V) :
    (NoLostDefinedApplications A S ∧ NoPartiallyRetainedValues A S) ↔
      A.IsClosed S := by
  constructor
  · rintro ⟨hNoLost, hNoPartial⟩
    intro F xs U hArgs hVal
    let ys : Fin (L.funcArity F) → S :=
      fun i => ⟨xs i, hArgs i⟩
    have hVal' : A.func F (Subtype.val ∘ ys) = some U := by
      change A.func F xs = some U
      exact hVal
    rcases hNoPartial F ys U hVal' with hSub | hDisjoint
    · exact hSub
    · rcases hNoLost F ys U hVal' with hEmpty | hMeet
      · simp [hEmpty]
      · exact (hDisjoint hMeet).elim
  · intro hClosed
    constructor
    · intro F xs U hVal
      have hSub : U ⊆ S :=
        hClosed F (Subtype.val ∘ xs) U
          (fun i => (xs i).2) hVal
      by_cases hEmpty : U = ∅
      · exact Or.inl hEmpty
      · right
        have hNonempty : U.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨y, hy⟩ := hNonempty
        exact ⟨y, hy, hSub hy⟩
    · intro F xs U hVal
      exact Or.inl
        (hClosed F (Subtype.val ∘ xs) U
          (fun i => (xs i).2) hVal)

/-- Exact map-level semantic square: the literal clipped weak
inclusion is FULL functional precisely when it is BOTH an induced
domain/output relational embedding and a source-defined partial
homomorphism of function structures on the SAME vertex map. -/
theorem clippedWeakFull_iff_inducedGraph_and_originalPartial
    (A : PartialSetStructure L V) (S : Set V) :
    (∃ e : Embedding (A.weakInduce S) A,
      e.toFun = (Subtype.val : S → V)) ↔
    ((∃ g : RelStructure.Embedding
        (domainGraph (A.weakInduce S)) (domainGraph A),
      g.toFun = (Subtype.val : S → V)) ∧
      IsOriginalPartialHomomorphism (A.weakInduce S) A
        (Subtype.val : S → V)) := by
  constructor
  · intro hFull
    have hClosed := (weakFullInclusion_iff_closed A S).mp hFull
    have hBoth := (noLost_and_noPartial_iff_closed A S).mpr hClosed
    exact ⟨(weakDomainGraphInclusion_iff_noLost A S).mpr hBoth.1,
      (clippedWeakInclusion_originalPartial_iff_noPartial A S).mpr hBoth.2⟩
  · rintro ⟨hGraph, hPartial⟩
    have hNoLost :=
      (weakDomainGraphInclusion_iff_noLost A S).mp hGraph
    have hNoPartial :=
      (clippedWeakInclusion_originalPartial_iff_noPartial A S).mp hPartial
    have hClosed :=
      (noLost_and_noPartial_iff_closed A S).mp ⟨hNoLost, hNoPartial⟩
    exact (weakFullInclusion_iff_closed A S).mpr hClosed

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.TrackASaturation

open StructuralRamsey.PartialSetStructure

/-- The existing two-output transversal, part-saturated example loses no
complete application, but fails the exact source-defined partial
homomorphism criterion (it retains one of two outputs). -/
theorem noLost_but_partiallyRetained :
    NoLostDefinedApplications examplePartial S ∧
      ¬ NoPartiallyRetainedValues examplePartial S := by
  refine ⟨noLost_even_though_not_closed.1, ?_⟩
  intro hNoPartial
  have hEqual :=
    (weakInduce_eq_wholeWeakInduce_iff_noPartial
      examplePartial S).mpr hNoPartial
  exact partSaturated_not_enough.2 hEqual

end StructuralRamsey.FunctionalPartite.TrackASaturation
