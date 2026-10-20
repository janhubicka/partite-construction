import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak
import PartiteConstruction.Relational.Homomorphism

/-!
# Complete-value tuples for partial set-valued functions

A relation indexed by (F,n) records a complete function value by an output
tuple of length n. Repeated output coordinates are allowed. The case n=0
records defined-empty, and an undefined application contributes no tuple.

This encoding commutes exactly with whole-fibre weak restriction. It is
not yet a canonical closure description: different output enumerations may
record the same value, and ambient active-root tags are not added here.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A complete tuple value survives whole-fibre weak restriction exactly
when it was the complete ambient value of those same output vertices. -/
theorem wholeWeakValue_eq_some_range_iff
    (S : Set V) (value : Option (Set V))
    {n : ℕ} (ys : Fin n → S) :
    wholeWeakValue S value = some (Set.range ys) ↔
      value = some (Set.range (Subtype.val ∘ ys)) := by
  constructor
  · intro h
    obtain ⟨U, hU, hUS, hRange⟩ :=
      (wholeWeakValue_eq_some_iff S value (Set.range ys)).mp h
    have hEq : U = Set.range (Subtype.val ∘ ys) := by
      ext y
      constructor
      · intro hy
        have hSubtype : (⟨y, hUS hy⟩ : S) ∈ Set.range ys := by
          rw [hRange]
          exact hy
        obtain ⟨i, hi⟩ := hSubtype
        exact ⟨i, congrArg Subtype.val hi⟩
      · rintro ⟨i, rfl⟩
        have hSubtype : ys i ∈ Set.range ys := ⟨i, rfl⟩
        rw [hRange] at hSubtype
        exact hSubtype
    rw [hU, hEq]
  · intro h
    have hSub : Set.range (Subtype.val ∘ ys) ⊆ S := by
      rintro y ⟨i, rfl⟩
      exact (ys i).2
    rw [h, wholeWeakValue_of_subset S _ hSub]
    congr 1
    ext y
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩

/-- Old relation symbols and complete-value symbols (F,n). The n output
coordinates enumerate the entire defined set, with repetitions permitted. -/
def wholeValueGraphLanguage (L : Language.{u}) : RelLanguage.{u} where
  Symbol := Sum L.RelSymbol (L.FuncSymbol × ℕ)
  arity
    | .inl R => L.relArity R
    | .inr (F, n) => L.funcArity F + n

/-- The complete finite-value tuple presentation of a partial set-valued
structure. Infinite fibres have no finite complete tuple in this language. -/
def wholeValueGraph (A : PartialSetStructure L V) :
    RelStructure (wholeValueGraphLanguage L) V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr (F, n), xs =>
        A.func F (fun i => xs (Fin.castAdd n i)) =
          some (Set.range (fun j : Fin n =>
            xs (Fin.natAdd (L.funcArity F) j)))

/-- Complete-value tuples commute with the intended whole-fibre weak
restriction on the EXACT original vertex subset. -/
theorem wholeWeakInduce_wholeValueGraph_rel_iff
    (A : PartialSetStructure L V) (S : Set V)
    (R : (wholeValueGraphLanguage L).Symbol)
    (xs : Fin ((wholeValueGraphLanguage L).arity R) → S) :
    (wholeValueGraph (wholeWeakInduce A S)).rel R xs ↔
      ((wholeValueGraph A).induce S).rel R xs := by
  cases R with
  | inl R =>
      rfl
  | inr symbol =>
      rcases symbol with ⟨F, n⟩
      exact wholeWeakValue_eq_some_range_iff S
        (A.func F (fun i => (xs (Fin.castAdd n i)).1))
        (fun j : Fin n => xs (Fin.natAdd (L.funcArity F) j))

/-- Identity map from the complete-value graph of a whole-fibre weak
restriction to the induced ambient complete-value graph. -/
def wholeWeakGraphToInduce
    (A : PartialSetStructure L V) (S : Set V) :
    RelStructure.Embedding
      (wholeValueGraph (wholeWeakInduce A S))
      ((wholeValueGraph A).induce S) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    exact (wholeWeakInduce_wholeValueGraph_rel_iff A S R xs).symm

/-- The inverse identity embedding: this presentation retains exactly
the whole weak relation tuples, including defined-empty applications. -/
def wholeWeakGraphFromInduce
    (A : PartialSetStructure L V) (S : Set V) :
    RelStructure.Embedding
      ((wholeValueGraph A).induce S)
      (wholeValueGraph (wholeWeakInduce A S)) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    exact wholeWeakInduce_wholeValueGraph_rel_iff A S R xs

/-- Source-defined homomorphisms preserve complete value tuples, even
when the vertex map identifies some of their output coordinates. -/
theorem IsOriginalPartialHomomorphism.to_wholeValueGraph_hom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (h : IsOriginalPartialHomomorphism A B f) :
    (wholeValueGraph A).IsHomomorphism (wholeValueGraph B) f := by
  intro R xs hxs
  cases R with
  | inl R =>
      exact h.1 R xs hxs
  | inr symbol =>
      rcases symbol with ⟨F, n⟩
      have hValue := h.2 F
        (fun i => xs (Fin.castAdd n i))
        (Set.range (fun j : Fin n =>
          xs (Fin.natAdd (L.funcArity F) j))) hxs
      have hImage :
          Structure.imageSet f
            (Set.range (fun j : Fin n => xs (Fin.natAdd (L.funcArity F) j))) =
          Set.range (fun j : Fin n => f (xs (Fin.natAdd (L.funcArity F) j))) := by
        ext y
        constructor
        · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
          exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨xs (Fin.natAdd (L.funcArity F) j), ⟨j, rfl⟩, rfl⟩
      change B.func F (fun i => f (xs (Fin.castAdd n i))) = _
      simpa only [hImage, Function.comp_apply] using hValue

end StructuralRamsey.PartialSetStructure
