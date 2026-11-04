import PartiteConstruction.Structure.PartialSetFunctionsDomainGraph

/-!
# Track A: faithful genuine partial-function domain-graph encoding

The two-relations-per-function encoding records the FULL information of a
partial Option(Set)-valued operation. The independent Dom_F relation
distinguishes none from some(∅); the output-incidence Graph_F relations
uniquely determine the complete value set of a defined application.

Thus the full relational encoding is injective ON THE SAME vertex type,
without closure assumptions, output transversality, finite arity bounds,
or restrictions on nullaries and repeated inputs.

This faithful source representation does NOT assert that every arbitrary
relational structure in the domainGraph language is canonically functional,
nor does it construct U-closed target completions or B-tree witnesses.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Equality of the independent domain and output-incidence graphs forces
equality of the original genuine Option(Set) partial-function structures.
Unlike the old graph-only encoding this detects defined-empty values. -/
theorem eq_of_domainGraph_eq
    (A B : PartialSetStructure L V)
    (h : domainGraph A = domainGraph B) : A = B := by
  cases A with
  | mk relA fnA =>
    cases B with
    | mk relB fnB =>
      change PartialSetStructure.mk relA fnA =
        PartialSetStructure.mk relB fnB
      congr 1
      · funext R xs
        have heq := congrArg
          (fun D : RelStructure (domainGraphLanguage L) V =>
            D.rel (.inl R) xs) h
        exact heq
      · funext F xs
        have hDom :
            (∃ U : Set V, fnA F xs = some U) ↔
              (∃ U : Set V, fnB F xs = some U) := by
          have heq := congrArg
            (fun D : RelStructure (domainGraphLanguage L) V =>
              D.rel (.inr (.inl F)) xs) h
          exact Iff.of_eq heq
        have hOutput (y : V) :
            (∃ U : Set V, fnA F xs = some U ∧ y ∈ U) ↔
              (∃ U : Set V, fnB F xs = some U ∧ y ∈ U) := by
          have heq := congrArg
            (fun D : RelStructure (domainGraphLanguage L) V =>
              D.rel (.inr (.inr F)) (Structure.funcTuple xs y)) h
          have hGraph :
              (∃ U : Set V, fnA F xs = some U ∧ y ∈ U) =
                (∃ U : Set V, fnB F xs = some U ∧ y ∈ U) := by
            simpa only [domainGraph, HasOutput,
              Structure.funcTuple_castSucc, Structure.funcTuple_last] using heq
          exact Iff.of_eq hGraph
        cases ha : fnA F xs with
        | none =>
          cases hb : fnB F xs with
          | none => exact ha.trans hb.symm
          | some T =>
            have hNone : ¬ (∃ U : Set V, fnA F xs = some U) := by
              simp [ha]
            have hSome : ∃ U : Set V, fnB F xs = some U := ⟨T, hb⟩
            exact (hNone (hDom.mpr hSome)).elim
        | some U =>
          cases hb : fnB F xs with
          | none =>
            have hSome : ∃ T : Set V, fnA F xs = some T := ⟨U, ha⟩
            have hNone : ¬ (∃ T : Set V, fnB F xs = some T) := by
              simp [hb]
            exact (hNone (hDom.mp hSome)).elim
          | some T =>
            have hUT : U = T := by
              ext y
              simpa [ha, hb] using (hOutput y)
            calc
              fnA F xs = some U := ha
              _ = some T := congrArg some hUT
              _ = fnB F xs := hb.symm

/-- Faithfulness as a compact equality equivalence, directly usable in
Track B/C when a canonical domain-graph representation is available. -/
theorem domainGraph_eq_iff
    (A B : PartialSetStructure L V) :
    domainGraph A = domainGraph B ↔ A = B := by
  constructor
  · exact eq_of_domainGraph_eq A B
  · intro h
    cases h
    rfl

end StructuralRamsey.PartialSetStructure
