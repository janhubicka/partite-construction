import PartiteConstruction.Functional.TrackCDomainEmptyFaithfulNative

/-!
# Track C: exact legal Dom/Empty native objects and inverse decoder

The 2019 cover-and-pullback route needs the native loose B-tree
construction to remain inside the genuinely partial Option(Set)
objects, not just preserve values on the original B copies.

This file gives an explicit local legal-model predicate for the
native domain/defined-empty encoding and proves that the legal
objects are exactly the canonical encodings of genuinely partial
structures on the SAME vertex carrier.

The remaining nontrivial F2 lemma is preservation of this legal
predicate under native free amalgams over FULL roots and under the
resulting loose B-tree constructions. That closure statement is
NOT assumed, and no Ramsey theorem follows from this module alone.
-/

namespace StructuralRamsey

universe u v

namespace Structure

variable {L : Language.{u}} {V : Type v}

/-- Local semantic compatibility of the native graph fibres with the
independent Dom_F and Empty_F relation symbols.
It forbids phantom positive fibres with Dom=false and disallows
Dom=true with an empty native fibre unless Empty=true. -/
def IsLegalDomainEmpty
    (C : Structure L.withDomainEmptyFlags V) : Prop :=
  ∀ (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V),
    (C.rel (.inr (.inl F)) xs ↔
       (C.func F xs).Nonempty ∨ C.rel (.inr (.inr F)) xs) ∧
    (C.rel (.inr (.inr F)) xs ↔
       C.rel (.inr (.inl F)) xs ∧ C.func F xs = ∅)

/-- Decode the native graph as the ENTIRE Option(Set) fibre when
Dom_F is present; otherwise the genuine partial value is undefined.
For arbitrary, possibly ILLEGAL native data this is still a
well-defined genuine partial structure. -/
def domainEmptyDecode (C : Structure L.withDomainEmptyFlags V) :
    PartialSetStructure L V where
  rel R xs := C.rel (.inl R) xs
  func F xs :=
    if C.rel (.inr (.inl F)) xs then some (C.func F xs) else none

private theorem exact_structure_ext
    {A B : Structure L.withDomainEmptyFlags V}
    (hrel : ∀ R xs, A.rel R xs ↔ B.rel R xs)
    (hfunc : ∀ F xs, A.func F xs = B.func F xs) : A = B := by
  cases A with
  | mk r f =>
    cases B with
    | mk s g =>
      have hr : r = s := by
        funext R xs
        exact propext (hrel R xs)
      have hf : f = g := by
        funext F xs
        exact hfunc F xs
      cases hr
      cases hf
      rfl

/-- Canonical Option(Set) encodings satisfy the exact two mask laws,
including the defined-empty case. -/
theorem domainEmptyEncode_isLegal
    (A : PartialSetStructure L V) :
    IsLegalDomainEmpty A.domainEmptyEncode := by
  intro F xs
  cases hA : A.func F xs with
  | none =>
      simp [PartialSetStructure.domainEmptyEncode,
        PartialSetStructure.Defined, hA]
  | some U =>
      by_cases hU : U = ∅
      · subst U
        simp [PartialSetStructure.domainEmptyEncode,
          PartialSetStructure.Defined, hA]
      · have hNonempty : U.Nonempty := by
          by_contra hn
          apply hU
          ext x
          constructor
          · intro hx
            exact (hn ⟨x, hx⟩).elim
          · simp
        simp [PartialSetStructure.domainEmptyEncode,
          PartialSetStructure.Defined, hA, hU, hNonempty]

/-- Under legal mask data, decoding and re-encoding reflect EVERY
native relation tuple (including Dom, Empty and original relations)
on the SAME exact vertex carrier. -/
theorem IsLegalDomainEmpty.decodeEncode_rel_iff
    {C : Structure L.withDomainEmptyFlags V}
    (hLegal : IsLegalDomainEmpty C)
    (R : L.withDomainEmptyFlags.RelSymbol)
    (xs : Fin (L.withDomainEmptyFlags.relArity R) → V) :
    C.domainEmptyDecode.domainEmptyEncode.rel R xs ↔ C.rel R xs := by
  rcases R with R | R
  · rfl
  rcases R with F | F
  · change
      (∃ U : Set V,
        (if C.rel (.inr (.inl F)) xs then
          some (C.func F xs) else none) = some U) ↔
        C.rel (.inr (.inl F)) xs
    by_cases hd : C.rel (.inr (.inl F)) xs <;> simp [hd]
  · change
      (if C.rel (.inr (.inl F)) xs then
        some (C.func F xs) else none) = some ∅ ↔
        C.rel (.inr (.inr F)) xs
    by_cases hd : C.rel (.inr (.inl F)) xs
    · have hEq : C.rel (.inr (.inr F)) xs ↔
          C.func F xs = ∅ := by
        simpa [hd] using (hLegal F xs).2
      simpa [hd] using hEq.symm
    · have hNotEmpty : ¬ C.rel (.inr (.inr F)) xs := by
        intro he
        exact hd (((hLegal F xs).2).mp he).1
      simp [hd, hNotEmpty]

/-- Under legal mask data, the re-encoded native function fibre is
literally the ORIGINAL native fibre, not an incidence-only subset. -/
theorem IsLegalDomainEmpty.decodeEncode_func
    {C : Structure L.withDomainEmptyFlags V}
    (hLegal : IsLegalDomainEmpty C)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    C.domainEmptyDecode.domainEmptyEncode.func F xs = C.func F xs := by
  change (if C.rel (.inr (.inl F)) xs then
    some (C.func F xs) else none).getD ∅ = C.func F xs
  by_cases hd : C.rel (.inr (.inl F)) xs
  · simp [hd]
  · have hn : ¬ (C.func F xs).Nonempty := by
      intro hValue
      exact hd (((hLegal F xs).1).mpr (Or.inl hValue))
    have hEmpty : C.func F xs = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hn ⟨x, hx⟩).elim
      · simp
    simp [hd, hEmpty]

/-- Every legal native object is literally the canonical Dom/Empty
encoding of its own decoded genuine partial structure. This uses
NO isomorphism, no extra vertices, and no artificial closure hull. -/
theorem IsLegalDomainEmpty.decodeEncode_eq
    {C : Structure L.withDomainEmptyFlags V}
    (hLegal : IsLegalDomainEmpty C) :
    C.domainEmptyDecode.domainEmptyEncode = C := by
  apply exact_structure_ext
  · intro R xs
    exact hLegal.decodeEncode_rel_iff R xs
  · intro F xs
    exact hLegal.decodeEncode_func F xs

end Structure

namespace PartialSetStructure

variable {L : Language.{u}} {V : Type v}

private theorem exact_partial_ext
    {A B : PartialSetStructure L V}
    (hrel : ∀ R xs, A.rel R xs ↔ B.rel R xs)
    (hfunc : ∀ F xs, A.func F xs = B.func F xs) : A = B := by
  cases A with
  | mk r f =>
    cases B with
    | mk s g =>
      have hr : r = s := by
        funext R xs
        exact propext (hrel R xs)
      have hf : f = g := by
        funext F xs
        exact hfunc F xs
      cases hr
      cases hf
      rfl

/-- Every genuine partial structure is reconstructed EXACTLY from
its faithful native Dom/Empty/value encoding, including some empty. -/
theorem domainEmptyDecode_encode_eq (A : PartialSetStructure L V) :
    A.domainEmptyEncode.domainEmptyDecode = A := by
  apply exact_partial_ext
  · intro R xs
    rfl
  · intro F xs
    change
      (if A.Defined F xs then
        some ((A.func F xs).getD ∅) else none) = A.func F xs
    cases hA : A.func F xs with
    | none =>
        simp [Defined, hA]
    | some U =>
        simp [Defined, hA]

end PartialSetStructure
end StructuralRamsey
