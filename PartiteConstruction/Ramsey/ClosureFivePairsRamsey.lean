import PartiteConstruction.Ramsey.ClosureFourPointUniversalFailure

/-! # Five independent closure pairs: the finite Ramsey input to Lemma 2.29

We complete the universal four-point obstruction with a finite initial
Ramsey witness C0. Its vertices are five disjoint root/output pairs.
There are exactly five A-copies, one at each output. By the finite
five-to-three pigeonhole statement, every two-colouring of the A-copies
has three identically coloured outputs. Any such triple determines an
induced copy of B: its root is the root associated with the first
chosen output, and the other two outputs are the remaining free vertices.

Both A and B are U-closed; C0 is U-closed as well, so every copy of A in
C0 is a U-substructure. The universal obstruction in
ClosureFourPointUniversalFailure.lean then shows that the literal
unqualified intrinsic-U-irreducible coverage conclusion of Lemma 2.29
cannot hold. We keep the argument separate from the still-viable
main multiamalgamation theorem and from its possible repairs.
-/

namespace StructuralRamsey.RelStructure.FourPointIntrinsicObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.TwoCopyIntrinsicObstruction

private abbrev PairVertex := Fin 5 × Bool

/-- There is one P-root and one R-output at each of five positions. -/
abbrev FivePairs : RelStructure Lang PairVertex where
  rel
    | false, t => (t ⟨0, by decide⟩).2 = false
    | true, t =>
        (t ⟨0, by decide⟩).2 = false ∧
        (t ⟨1, by decide⟩).2 = true ∧
        (t ⟨0, by decide⟩).1 = (t ⟨1, by decide⟩).1

/-- The only copies of A are singleton non-root outputs. -/
private def outputCopy (i : Fin 5) : Embedding One FivePairs where
  toFun := fun _ => (i, true)
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change (true = false) ↔ False
      decide
    | true =>
      change (true = false ∧ true = true ∧ i = i) ↔ False
      decide

/-- A finite combinatorial statement independent of the structures:
any Boolean labelling of five points has three pairwise distinct
points with the same label. -/
private theorem fivePigeon :
    ∀ c : Fin 5 → Bool,
      ∃ i j k : Fin 5,
        i < j ∧ j < k ∧
          c i = c j ∧ c i = c k := by
  decide

/-- The selected B-copy occupies a root/output pair at i and two
additional outputs at j and k. -/
private def placedVertex (i j k : Fin 5) : Fin 4 → PairVertex
  | 0 => (i, false)
  | 1 => (i, true)
  | 2 => (j, true)
  | 3 => (k, true)

/-- The selected triple gives a full induced copy of B. -/
private def placedFour (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Embedding Four FivePairs where
  toFun := placedVertex i j k
  injective := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [placedVertex, Prod.mk.injEq]
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change
        (placedVertex i j k (x (0 : Fin 1))).2 = false ↔
        x (0 : Fin 1) = 0
      fin_cases hx : x (0 : Fin 1) <;>
        simp [hx, placedVertex]
    | true =>
      change
        ((placedVertex i j k (x (0 : Fin 2))).2 = false ∧
         (placedVertex i j k (x (1 : Fin 2))).2 = true ∧
         (placedVertex i j k (x (0 : Fin 2))).1 =
           (placedVertex i j k (x (1 : Fin 2))).1) ↔
        (x (0 : Fin 2) = 0 ∧ x (1 : Fin 2) = 1)
      fin_cases hx : x (0 : Fin 2) <;>
        fin_cases hy : x (1 : Fin 2) <;>
        simp_all [placedVertex]

private theorem oneNonRoot (e : Embedding One Four) :
    e 0 ≠ 0 := by
  intro he
  have hP : Four.rel false (e ∘ (fun _ : Fin 1 => (0 : Fin 1))) := by
    change e 0 = (0 : Fin 4)
    exact he
  have hA : One.rel false (fun _ : Fin 1 => (0 : Fin 1)) :=
    (e.map_rel_iff false (fun _ : Fin 1 => 0)).mp hP
  exact hA

private theorem placedOneCopy
    (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (e : Embedding One Four) :
    ((placedFour i j k hij hik hjk).comp e =
      outputCopy i) ∨
    ((placedFour i j k hij hik hjk).comp e =
      outputCopy j) ∨
    ((placedFour i j k hij hik hjk).comp e =
      outputCopy k) := by
  have hne := oneNonRoot e
  fin_cases h : e 0
  · exact False.elim (hne h)
  · left
    apply Embedding.ext
    intro a
    fin_cases a
    simp [placedFour, placedVertex, outputCopy, h]
  · right
    left
    apply Embedding.ext
    intro a
    fin_cases a
    simp [placedFour, placedVertex, outputCopy, h]
  · right
    right
    apply Embedding.ext
    intro a
    fin_cases a
    simp [placedFour, placedVertex, outputCopy, h]

/-- The promised explicit Ramsey witness with five root/output pairs. -/
theorem fivePairs_arrow :
    StructuralRamsey.Arrow One Four FivePairs Bool := by
  intro χ
  let c : Fin 5 → Bool := fun i => χ (outputCopy i)
  obtain ⟨i, j, k, hij, hjk, hcij, hcik⟩ := fivePigeon c
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  have hik' : i ≠ k := ne_of_lt (lt_trans hij hjk)
  let b : Embedding Four FivePairs :=
    placedFour i j k hij' hik' hjk'
  refine ⟨b, ?_⟩
  have hColour (e : Embedding One Four) :
      χ (b.comp e) = χ (outputCopy i) := by
    rcases placedOneCopy i j k hij' hik' hjk' e with
        he | he | he
    · exact congrArg χ he
    · calc
        χ (b.comp e) = χ (outputCopy j) := congrArg χ he
        _ = χ (outputCopy i) := hcij.symm
    · calc
        χ (b.comp e) = χ (outputCopy k) := congrArg χ he
        _ = χ (outputCopy i) := hcik.symm
  intro e1 e2
  exact (hColour e1).trans (hColour e2).symm

/-- The P-root at i is an induced copy of the prescribed singleton
closure root. -/
private def rootAt (i : Fin 5) : Embedding Root FivePairs where
  toFun := fun _ => (i, false)
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change (false = false) ↔ (false = false)
      rfl
    | true =>
      change (false = false ∧ false = true ∧ i = i) ↔
        (true = false)
      simp

/-- The initial Ramsey witness is U-closed on all five closure pairs. -/
theorem fivePairs_isUClosed : IsUClosed rules FivePairs := by
  intro r hr
  have hrule : r = rule := by
    simpa [rules] using hr
  subst r
  constructor
  · intro t ht
    let i : Fin 5 := (t (0 : Fin 2)).1
    refine ⟨rootAt i, ?_⟩
    intro k
    fin_cases k
    change t 0 = (i, false)
    apply Prod.ext
    · rfl
    · exact ht.1
  · intro e
    let i : Fin 5 := (e 0).1
    have hp : (e 0).2 = false := by
      have hP : Root.rel false (fun _ : Fin 1 => (0 : Fin 1)) := by
        decide
      have hC : FivePairs.rel false (e ∘ (fun _ : Fin 1 => (0 : Fin 1))) :=
        (e.map_rel_iff false (fun _ : Fin 1 => 0)).mpr hP
      exact hC
    let t : Fin 2 → PairVertex := ![(i, false), (i, true)]
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · change (false = false) ∧ (true = true) ∧ i = i
      exact ⟨rfl, rfl, rfl⟩
    · intro k
      fin_cases k
      change (i, false) = e 0
      apply Prod.ext
      · rfl
      · exact hp.symm
    · intro s hs
      funext k
      fin_cases k
      · exact hs.2 (0 : Fin 1)
      · have hsroot : s 0 = e 0 := hs.2 (0 : Fin 1)
        have hsR : (s 0).2 = false ∧
            (s 1).2 = true ∧ (s 0).1 = (s 1).1 := hs.1
        apply Prod.ext
        · change (s 1).1 = i
          exact hsR.2.2.symm.trans (congrArg Prod.fst hsroot).symm
        · exact hsR.2.1

/-- The A-copies, being U-closed, are all U-substructures of this
U-closed ambient Ramsey witness. -/
theorem every_one_isUSubstructure
    (e : Embedding One FivePairs) :
    IsUSubstructure rules FivePairs (Set.range e) :=
  e.range_isUSubstructure one_isUClosed fivePairs_isUClosed

/-- The exact hypothesis of published Lemma 2.29 for A, B and C0 is
satisfied by this finite example. -/
theorem fivePairs_lemma229_hypotheses :
    IsUClosed rules One ∧
    IsUClosed rules Four ∧
    StructuralRamsey.Arrow One Four FivePairs Bool ∧
    (∀ e : Embedding One FivePairs,
      IsUSubstructure rules FivePairs (Set.range e)) :=
  ⟨one_isUClosed, four_isUClosed, fivePairs_arrow,
    every_one_isUSubstructure⟩

/-- The full existential conclusion of the printed Lemma 2.29 is
false for this finite input if U-irreducibility is interpreted exactly
as indecomposability into intrinsically U-closed proper substructures.
The assertion includes the stronger published projection requirement;
it is refuted already without using that projection. -/
theorem lemma229_intrinsic_formulation_false :
    ¬ ∃ (W : Type) (_ : Finite W)
        (C : RelStructure Lang W),
        IsUClosed rules C ∧
        StructuralRamsey.Arrow One Four C Bool ∧
        AllIntrinsicUIrreducibleTestsEmbed rules C Four ∧
        (∃ f : W → PairVertex,
          IsUHomomorphismEmbedding rules C FivePairs f) := by
  rintro ⟨W, _, C, hClosed, hArrow, hCoverage, _⟩
  exact no_UClosed_Ramsey_and_intrinsic_coverage
    hClosed hArrow hCoverage

end StructuralRamsey.RelStructure.FourPointIntrinsicObstruction
