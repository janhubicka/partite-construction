import PartiteConstruction.Ramsey.ClosureWeakTestIntrinsicObstruction

/-! # A finite two-copy weak-test regression for intrinsic U-irreducibility

Language: a unary root predicate P and a binary closure relation R.
A B-copy has a P-root r, a non-P output o, and the tuple R(r,o).
The ambient picture consists of two disjoint B-copies.

The induced three-vertex weak test {r_left, r_right, o_right} omits
the unique closure output of r_left, and thus is intrinsically
U-irreducible according to the literal 2019 Definition 2.15. It cannot
embed in one B-copy (B has just two vertices). This is an elementary
obstruction to the *unqualified* 'no new U-irreducibles' invariant
asserted for the initial disjoint picture in Lemma 2.29.

This file first certifies the finite combinatorial data and the
intrinsic weak-test failure. It is NOT by itself a counterexample to
the existence assertion of the complete Lemma 2.29.
-/

namespace StructuralRamsey.RelStructure.TwoCopyIntrinsicObstruction

open StructuralRamsey.RelStructure

abbrev Lang : RelLanguage where
  Symbol := Bool
  arity
    | false => 1
    | true => 2

abbrev Root : RelStructure Lang (Fin 1) where
  rel R _ := R = false

private abbrev Base : RelStructure Lang (Fin 2) where
  rel
    | false, t => t ⟨0, by decide⟩ = 0
    | true, t => t ⟨0, by decide⟩ = 0 ∧ t ⟨1, by decide⟩ = 1

private abbrev TwoCopies : RelStructure Lang (Bool × Fin 2) where
  rel R t :=
    ∃ side : Bool,
      (∀ i : Fin (Lang.arity R), (t i).1 = side) ∧
        Base.rel R (fun i => (t i).2)

abbrev rule : ClosureRule Lang where
  symbol := true
  rootSize := 1
  rootPositive := by decide
  rootStrict := by decide
  root := Root
  rootIrreducible := by
    intro x y hxy
    exact (hxy (Subsingleton.elim x y)).elim

abbrev rules : ClosureDescription Lang := {rule}

private abbrev rootInFirst : Embedding Root TwoCopies where
  toFun := fun _ => (false, 0)
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change (∃ side : Bool,
        (∀ i : Fin 1, false = side) ∧ (0 : Fin 2) = 0) ↔ (false = false)
      constructor
      · intro _; rfl
      · intro _; exact ⟨false, (fun _ => rfl), rfl⟩
    | true =>
      change (∃ side : Bool,
        (∀ i : Fin 2, false = side) ∧
          ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 1)) ↔ (true = false)
      constructor
      · rintro ⟨_, _, h⟩
        exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h.2)
      · intro h
        cases h

private abbrev leftCopy : Embedding Base TwoCopies where
  toFun := fun x => (false, x)
  injective := by
    intro x y h
    exact congrArg Prod.snd h
  map_rel_iff := by
    intro R x
    change (∃ side : Bool,
      (∀ i : Fin (Lang.arity R), false = side) ∧ Base.rel R x) ↔
      Base.rel R x
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      exact ⟨false, (fun _ => rfl), h⟩

private abbrev rightCopy : Embedding Base TwoCopies where
  toFun := fun x => (true, x)
  injective := by
    intro x y h
    exact congrArg Prod.snd h
  map_rel_iff := by
    intro R x
    change (∃ side : Bool,
      (∀ i : Fin (Lang.arity R), true = side) ∧ Base.rel R x) ↔
      Base.rel R x
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      exact ⟨true, (fun _ => rfl), h⟩

private abbrev badSet : Set (Bool × Fin 2) :=
  {z | z.1 = true ∨ z = (false, 0)}

private def selected : Fin 3 → badSet
  | 0 => ⟨(false, 0), Or.inr rfl⟩
  | 1 => ⟨(true, 0), Or.inl rfl⟩
  | 2 => ⟨(true, 1), Or.inl rfl⟩

private theorem selected_injective : Function.Injective selected := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [selected]

private theorem bad_root_in :
    ∀ k : Fin rule.rootSize, rootInFirst k ∈ badSet := by
  intro k
  exact Or.inr rfl

private theorem bad_missing :
    ∀ t : Fin (Lang.arity rule.symbol) → (Bool × Fin 2),
      TwoCopies.rel rule.symbol t →
      (∀ k : Fin rule.rootSize,
         t (k.castLE rule.rootLE) = rootInFirst k) →
      ∃ j : Fin (Lang.arity rule.symbol), t j ∉ badSet := by
  intro t ht hAlign
  obtain ⟨side, hUniform, hRel⟩ := ht
  have ht0 : t (0 : Fin 2) = (false, 0) := by
    simpa [rule, rootInFirst, Lang] using hAlign (0 : Fin 1)
  have hside : side = false := by
    calc
      side = (t 0).1 := (hUniform 0).symm
      _ = false := congrArg Prod.fst ht0
  have hout : (t (1 : Fin 2)).2 = (1 : Fin 2) := by
    change (t 0).2 = (0 : Fin 2) ∧
      (t 1).2 = (1 : Fin 2) at hRel
    exact hRel.2
  have ht1 : t (1 : Fin 2) = (false, 1) := by
    apply Prod.ext
    · exact (hUniform 1).trans hside
    · exact hout
  refine ⟨1, ?_⟩
  simp [badSet, ht1]

/-- Fully finite intrinsic U-irreducibility of the three-vertex
weak induced test: it has a P-root but omits its R-output. -/
theorem weakTest_isUIrreducible :
    IsUIrreducible rules (TwoCopies.induce badSet) :=
  IsUIrreducible.of_missing_tuple_in_weak_test
    rule (by simp [rules]) rootInFirst badSet
    bad_root_in bad_missing

/-- Both B-copies are present as exact induced embeddings. -/
theorem two_induced_B_copies :
    Nonempty (Embedding Base TwoCopies) ∧
      Nonempty (Embedding Base TwoCopies) :=
  ⟨⟨leftCopy⟩, ⟨rightCopy⟩⟩

/-- The bad weak test meets both exclusive copies. -/
theorem weakTest_crosses_both_copies :
    (¬ ∀ z : badSet, ∃ x : Fin 2, z.1 = leftCopy x) ∧
      (¬ ∀ z : badSet, ∃ x : Fin 2, z.1 = rightCopy x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h ⟨(true, 0), Or.inl rfl⟩
    have hbad : true = false := congrArg Prod.fst hx
    cases hbad
  · intro h
    obtain ⟨x, hx⟩ := h ⟨(false, 0), Or.inr rfl⟩
    have hbad : false = true := congrArg Prod.fst hx
    cases hbad

/-- The literal 'every U-irreducible weak test is contained in a
B-copy' property fails already in a two-copy picture. -/
theorem twoCopies_not_all_intrinsic_tests_in_B :
    ¬ AllIntrinsicUIrreducibleTestsEmbed rules TwoCopies Base := by
  classical
  letI : Fintype badSet := Fintype.ofFinite badSet
  have hLarge : Fintype.card (Fin 2) < Fintype.card badSet := by
    have h3 : 3 ≤ Fintype.card badSet := by
      simpa using (Fintype.card_le_of_injective selected selected_injective)
    exact lt_of_lt_of_le (by decide : 2 < 3) h3
  exact not_allIntrinsicUIrreducibleTestsEmbed_of_large_missing_test
    rule (by simp [rules]) rootInFirst badSet
    bad_root_in bad_missing hLarge


/-- The singleton closure root embeds at the distinguished P-vertex. -/
private abbrev rootInBase : Embedding Root Base where
  toFun := fun _ => 0
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change ((0 : Fin 2) = 0) ↔ (false = false)
      simp
    | true =>
      change (((0 : Fin 2) = 0) ∧ ((0 : Fin 2) = 1)) ↔ (true = false)
      simp

/-- Each B-copy is genuinely U-closed. -/
theorem base_isUClosed : IsUClosed rules Base := by
  intro r hr
  have hrule : r = rule := by
    simpa [rules] using hr
  subst r
  constructor
  · intro t ht
    refine ⟨rootInBase, ?_⟩
    intro k
    fin_cases k
    exact ht.1
  · intro e
    have he : e = rootInBase := by
      apply Embedding.ext
      intro k
      fin_cases k
      have hp : Base.rel false
          (e ∘ (fun _ : Fin 1 => (0 : Fin 1))) :=
        (e.map_rel_iff false (fun _ : Fin 1 => 0)).mpr (by decide)
      change e 0 = (0 : Fin 2) at hp
      exact hp
    rw [he]
    refine ⟨![0, 1], ⟨?_, ?_⟩, ?_⟩
    · decide
    · intro k
      fin_cases k
      rfl
    · intro t ht
      funext j
      fin_cases j
      · exact ht.1.1
      · exact ht.1.2

private abbrev Empty : RelStructure Lang (Fin 0) where
  rel _ _ := False

private abbrev emptyToBase : Embedding Empty Base where
  toFun := fun x => x.elim0
  injective := by
    intro x
    exact x.elim0
  map_rel_iff := by
    intro R x
    cases R with
    | false => exact (x 0).elim0
    | true => exact (x 0).elim0

private theorem empty_isUClosed : IsUClosed rules Empty := by
  intro r _
  constructor
  · intro t ht
    exact False.elim ht
  · intro e
    exact (e ⟨0, r.rootPositive⟩).elim0

/-- The actual picture is a free amalgam of two copies of the
U-closed structure B over the empty (and U-closed) common root. -/
theorem twoCopies_isFreeAmalgam :
    IsFreeAmalgam emptyToBase emptyToBase leftCopy rightCopy := by
  constructor
  · rintro ⟨side, x⟩
    cases side with
    | false => exact Or.inl ⟨x, rfl⟩
    | true => exact Or.inr ⟨x, rfl⟩
  · intro a b
    constructor
    · intro h
      have hbad : false = true := congrArg Prod.fst h
      cases hbad
    · rintro ⟨d, _, _⟩
      exact d.elim0
  · intro R t
    constructor
    · rintro ⟨side, hUniform, hRel⟩
      cases side with
      | false =>
        refine Or.inl ⟨(fun i => (t i).2), hRel, ?_⟩
        funext i
        apply Prod.ext
        · exact hUniform i
        · rfl
      | true =>
        refine Or.inr ⟨(fun i => (t i).2), hRel, ?_⟩
        funext i
        apply Prod.ext
        · exact hUniform i
        · rfl
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨false, (fun _ => rfl), hx⟩
      · exact ⟨true, (fun _ => rfl), hx⟩

/-- The two-copy picture is U-closed, despite containing a
non-U-closed weak test which is intrinsically U-irreducible. -/
theorem twoCopies_isUClosed : IsUClosed rules TwoCopies :=
  twoCopies_isFreeAmalgam.isUClosed
    empty_isUClosed base_isUClosed base_isUClosed

end StructuralRamsey.RelStructure.TwoCopyIntrinsicObstruction
