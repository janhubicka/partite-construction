import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track A: exact domain predicates under the two weak conventions

On an exact weak carrier S, with input tuple already in S:

* clipped weak restriction is defined iff the ambient application has
  some(U) with U empty, OR with at least one surviving output in U∩S;
* whole-fibre weak restriction is defined iff the ambient application has
  some(U) and its ENTIRE output U is contained in S.

Both results retain some(∅), exclude none, and support nullary symbols,
repetitions, and arbitrary multivalued outputs. The ambient domain relation
cannot in general be induced onto S using the intrinsic weak operation:
a lost output erases a formerly defined application. This is exactly why
an ambient OLD domain mask must be carried separately in the 2019 encoding.

No function-closedness or auxiliary target-completion hypothesis is used.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Precise preservation of the domain bit by CLIPPED weak restriction. -/
theorem weakInduce_defined_iff_exact
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (A.weakInduce S).Defined F xs ↔
      ∃ U : Set V,
        A.func F (Subtype.val ∘ xs) = some U ∧
        (U = ∅ ∨ (U ∩ S).Nonempty) := by
  change (∃ T : Set S,
    weakValue S (A.func F (Subtype.val ∘ xs)) = some T) ↔ _
  constructor
  · rintro ⟨T, hT⟩
    cases hVal : A.func F (Subtype.val ∘ xs) with
    | none =>
      simp [weakValue, hVal] at hT
    | some U =>
      refine ⟨U, rfl, ?_⟩
      by_cases hU : U.Nonempty
      · right
        by_contra hMeet
        simp [weakValue, hVal, hU, hMeet] at hT
      · left
        ext x
        constructor
        · intro hx
          exact (hU ⟨x, hx⟩).elim
        · simp
  · rintro ⟨U, hVal, hSurvive⟩
    rcases hSurvive with hEmpty | hMeet
    · subst U
      refine ⟨∅, ?_⟩
      simp [weakValue, hVal]
    · obtain ⟨y, hyU, hyS⟩ := hMeet
      have hU : U.Nonempty := ⟨y, hyU⟩
      refine ⟨{z : S | z.1 ∈ U}, ?_⟩
      simp [weakValue, hVal, hU, show (U ∩ S).Nonempty from
        ⟨y, hyU, hyS⟩]

/-- Precise preservation of the domain bit by WHOLE-fibre deletion. -/
theorem wholeWeakInduce_defined_iff_exact
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (A.wholeWeakInduce S).Defined F xs ↔
      ∃ U : Set V,
        A.func F (Subtype.val ∘ xs) = some U ∧ U ⊆ S := by
  change (∃ T : Set S,
    wholeWeakValue S (A.func F (Subtype.val ∘ xs)) = some T) ↔ _
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨U, hU, hUS, _⟩ :=
      (wholeWeakValue_eq_some_iff S _ T).mp hT
    exact ⟨U, hU, hUS⟩
  · rintro ⟨U, hU, hUS⟩
    refine ⟨{z : S | z.1 ∈ U}, ?_⟩
    rw [hU]
    exact wholeWeakValue_of_subset S U hUS

/-- A clipped source-defined input was already defined in the ambient
structure; the converse fails when every output is lost. -/
theorem weakInduce_defined_implies_ambient
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (h : (A.weakInduce S).Defined F xs) :
    A.Defined F (Subtype.val ∘ xs) := by
  obtain ⟨U, hU, _⟩ := (weakInduce_defined_iff_exact A S F xs).mp h
  exact ⟨U, hU⟩

end StructuralRamsey.PartialSetStructure
