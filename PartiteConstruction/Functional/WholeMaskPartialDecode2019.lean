import PartiteConstruction.Functional.WholeMaskRelativeClosure2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Genuinely partial complete-mask decoder with an independent domain bit

The OLD complete-mask relational language remembers both active domain
tuples and COMPLETE output tuples. A defined-empty output has a true
complete graph relation with a mask of size zero; an undefined input
has no such graph relation. Unlike ordinary single-output incidence
decoders, this distinction is preserved.

A complete OLD value witness names one primitive F input x, its
distinct-root equality pattern (arbitrary repetitions allowed), an
output-part mask, and a tuple enumerating its ENTIRE output set.
The decoder chooses a witness value if one exists, returning some U,
and returns none if no witness exists. It is defined on every OLD
relational structure; inconsistent OLD data may yield multiple
different witnesses, so the decoder is faithful only under a
separately proved uniqueness condition.

The final protected B-copy U-closed target supplies precisely that
condition through the cross-pattern output theorem. A further
positive-domain existence bridge is needed before equating the
decoder's domain to all OLD domain records. Neither is assumed here.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V : Type v}

/-- The OLD graph records an ENTIRE defined function value U at input
tuple x; the equality pattern is allowed to use repeated primitive
input arguments, but its enumerated DISTINCT root is surjective. -/
def HasWholeMaskValue
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U : Set V) : Prop :=
  ∃ (m : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (hr : Function.Surjective r)
    (q : Language.CompleteOutputParts P)
    (t : Fin (m + q.size) → V),
    E.rel (.inr (.inr
      ((⟨F, m, r, hr⟩ : Language.FunctionInputPattern L), q))) t ∧
    (∀ i : Fin (L.funcArity F),
      x i = t (Fin.castAdd q.size (r i))) ∧
    U = Set.range (fun j : Fin q.size => t (Fin.natAdd m j))

/-- Independent OLD active domain record, including a mask of length
zero. No output occurrence is required for this predicate. -/
def HasWholeMaskDomain
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) : Prop :=
  ∃ (m : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (hr : Function.Surjective r)
    (q : Language.CompleteOutputParts P)
    (root : Fin m → V),
    E.rel (.inr (.inl
      ((⟨F, m, r, hr⟩ : Language.FunctionInputPattern L), q))) root ∧
    (∀ i : Fin (L.funcArity F), x i = root (r i))

/-- Decode complete OLD whole-set output relations to a genuinely
partial Option(Set) function. Defined-empty is retained as some ∅,
never identified with none. The choice is faithful whenever there is
at most one complete value set for each (F,x). -/
noncomputable def wholeMaskPartialDecode
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) :
    PartialSetStructure L V where
  rel R xs := E.rel (.inl R) xs
  func F xs := by
    classical
    exact if h : ∃ U : Set V, HasWholeMaskValue E F xs U
      then some (Classical.choose h) else none

/-- A decoded operation is undefined EXACTLY when it has no complete
OLD graph value witness. No uniqueness hypothesis is needed. -/
theorem wholeMaskPartialDecode_func_none_iff
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    (E.wholeMaskPartialDecode).func F x = none ↔
      ¬ ∃ U : Set V, HasWholeMaskValue E F x U := by
  classical
  by_cases h : ∃ U : Set V, HasWholeMaskValue E F x U
  · simp [wholeMaskPartialDecode, h]
  · simp [wholeMaskPartialDecode, h]

/-- Once all complete OLD graph witnesses of F(x) have the same
underlying output set, the decoder realizes precisely every one of
them (including U = ∅). This is the map-level comparison theorem
needed to reconstruct actual functions from covered tagged targets. -/
theorem wholeMaskPartialDecode_func_some_iff
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (hUnique : ∀ U T : Set V,
      HasWholeMaskValue E F x U →
      HasWholeMaskValue E F x T → U = T)
    (U : Set V) :
    (E.wholeMaskPartialDecode).func F x = some U ↔
      HasWholeMaskValue E F x U := by
  classical
  by_cases h : ∃ T : Set V, HasWholeMaskValue E F x T
  · have hc : HasWholeMaskValue E F x (Classical.choose h) :=
      Classical.choose_spec h
    constructor
    · intro hSome
      have hEq : Classical.choose h = U := by
        have hs : some (Classical.choose h) = some U := by
          simpa [wholeMaskPartialDecode, h] using hSome
        exact Option.some.inj hs
      rw [← hEq]
      exact hc
    · intro hU
      have heq : Classical.choose h = U :=
        hUnique _ _ hc hU
      simpa [wholeMaskPartialDecode, h, heq]
  · constructor
    · intro hSome
      have hn : False := by
        simpa [wholeMaskPartialDecode, h] using hSome
      exact hn.elim
    · intro hU
      exact (h ⟨U,hU⟩).elim

/-- A complete OLD graph tuple determines a domain relation when OLD
complete-mask root validity holds. This is the safe one-way direction;
the converse needs closure/completion and defined-empty reductions. -/
theorem HasValidCompleteMaskDomains.domain_of_value
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (hValid : HasValidCompleteMaskDomains E)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U : Set V)
    (h : HasWholeMaskValue E F x U) :
    HasWholeMaskDomain E F x := by
  obtain ⟨m, r, hr, q, t, hGraph, hArgs, _⟩ := h
  let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  let root : Fin m → V := fun i => t (Fin.castAdd q.size i)
  have hDomain :=
    (hValid pat q t hGraph).2
  exact ⟨m, r, hr, q, root, hDomain, hArgs⟩

end StructuralRamsey.RelStructure
