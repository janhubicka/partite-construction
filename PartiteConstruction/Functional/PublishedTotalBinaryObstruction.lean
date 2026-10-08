import PartiteConstruction.Functional.PublishedSparseningTarget
import PartiteConstruction.Functional.RankedTreeReduct

/-! # A counterexample to the published full-functional sparsening statement

Let F(x,y)={x} on finite sets. Every injection is a full embedding, and
three points are Ramsey for two points under two-colourings of singletons.
The one-, two-, and three-point structures are all functionally irreducible.

A FULL homomorphism to the three-point structure forces every binary input
of its source to have a value. This makes the source irreducible, so a full
homomorphism-embedding into the three-point structure is injective. At local
rank 3 the whole source must complete into a strict tree of two-point bases.
Irreducibility localizes its embedded image to one two-point base copy.
But no structure embedding into two points is Ramsey for a monochromatic
pair of singletons.

Thus the original existential conclusion, not merely the canonical proof,
fails under the survey's literal full-fibre homomorphism definition. Clause
(3) is not used in the contradiction. This does not concern the verified
relational theorem, or a version with a weak EHN global projection.
-/

namespace StructuralRamsey.Structure.PublishedTotalBinaryObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- One binary set-valued function, with no relation symbols. -/
abbrev language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 2

/-- The left-projection algebra on a carrier. -/
def algebra (V : Type) : Structure language V where
  rel R := Empty.elim R
  func _ x := {x (0 : Fin 2)}

abbrev A := algebra (Fin 1)
abbrev B := algebra (Fin 2)
abbrev D := algebra (Fin 3)

/-- Nonempty fibres on all binary input pairs. -/
def Total {V : Type} (C : Structure language V) : Prop :=
  ∀ x y : V, (C.func () ![x, y]).Nonempty

theorem algebra_total (V : Type) : Total (algebra V) := by
  intro x y
  exact ⟨x, rfl⟩

/-- A total binary operation precludes a free decomposition crossing two
proper closed sides: the input pair itself must belong to one side. -/
theorem total_irreducible {V : Type} {C : Structure language V}
    (htotal : Total C) : C.Irreducible := by
  intro H E F W Root Left Right Whole sL sR iL iR hfree e
  by_cases hleft : ∀ c : V, ∃ a : E, e c = iL a
  · exact Or.inl hleft
  · right
    push_neg at hleft
    obtain ⟨c, hc⟩ := hleft
    intro d
    obtain ⟨z, hz⟩ := htotal c d
    have hValue : e z ∈ Whole.func () (e ∘ ![c, d]) := by
      have h : e z ∈ imageSet e (C.func () ![c, d]) := ⟨z, hz, rfl⟩
      rw [e.map_func () ![c, d]] at h
      exact h
    rcases (hfree.func_iff () (e ∘ ![c, d]) (e z)).mp hValue with
      ⟨args, out, _, heq, _⟩ | ⟨args, out, _, heq, _⟩
    · exact (hc (args (0 : Fin 2)) (congrFun heq (0 : Fin 2))).elim
    · exact ⟨args (1 : Fin 2), congrFun heq (1 : Fin 2)⟩

/-- Full homomorphisms reflect totality of the target's binary operation. -/
theorem total_of_full_projection
    {V : Type} {C : Structure language V} {p : V → Fin 3}
    (hp : C.IsHomomorphism D p) : Total C := by
  intro x y
  have hTarget : p x ∈ D.func () (p ∘ ![x, y]) := rfl
  rw [← hp.2 () ![x, y]] at hTarget
  obtain ⟨z, hz, _⟩ := hTarget
  exact ⟨z, hz⟩

/-- Every injection between left-projection algebras is a full embedding. -/
def ofInjection {V W : Type} (f : V → W) (hf : Function.Injective f) :
    Embedding (algebra V) (algebra W) where
  toFun := f
  injective := hf
  map_rel_iff R := Empty.elim R
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change z = x (0 : Fin 2) at hz
      change f z = f (x (0 : Fin 2))
      exact congrArg f hz
    · intro hy
      change y = f (x (0 : Fin 2)) at hy
      exact ⟨x (0 : Fin 2), rfl, hy.symm⟩

/-- An embedding of the one-point algebra, specified by its value. -/
def point {V : Type} (x : V) : Embedding A (algebra V) :=
  ofInjection (fun _ => x) (fun _ _ _ => Subsingleton.elim _ _)

/-- The 3 -> (2)^1_2 pigeonhole arrow in the exact full-function language. -/
theorem three_ramsey_two : Arrow A B D (Fin 2) := by
  classical
  intro χ
  let colour : Fin 3 → Fin 2 := fun x => χ (point x)
  have hnot : ¬ Function.Injective colour := by
    intro h
    have hcard := Fintype.card_le_of_injective colour h
    norm_num at hcard
  have hpair : ∃ i j : Fin 3, i ≠ j ∧ colour i = colour j := by
    by_contra h
    apply hnot
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  obtain ⟨i, j, hij, hcol⟩ := hpair
  let f : Fin 2 → Fin 3 := ![i, j]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hij hab).elim
    · exact (hij hab.symm).elim
    · rfl
  let emb : Embedding B D := ofInjection f hfinj
  refine ⟨emb, ?_⟩
  intro e₁ e₂
  have hcomp (e : Embedding A B) : emb.comp e = point (f (e 0)) := by
    apply Embedding.ext
    intro a
    have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
    subst a
    rfl
  rw [hcomp e₁, hcomp e₂]
  change colour (f (e₁ 0)) = colour (f (e₂ 0))
  fin_cases h₁ : e₁ 0 <;> fin_cases h₂ : e₂ 0
  · rfl
  · exact hcol
  · exact hcol.symm
  · rfl

/-- A witness embedding into B cannot be Ramsey for a monochromatic pair:
colour a singleton by its image in the two-point carrier. -/
theorem no_ramsey_with_embedding_into_two
    {V : Type} {C : Structure language V}
    (hArrow : Arrow A B C (Fin 2)) (j : Embedding C B) : False := by
  let χ : Embedding A C → Fin 2 := fun e => j (e 0)
  obtain ⟨f, hf⟩ := hArrow χ
  have heq : j (f (0 : Fin 2)) = j (f (1 : Fin 2)) :=
    hf (point (0 : Fin 2)) (point (1 : Fin 2))
  have hbad : (0 : Fin 2) = 1 := f.injective (j.injective heq)
  exact (by decide : (0 : Fin 2) ≠ 1) hbad

/-- Clauses (1) and (2) with n=3 already contradict the Ramsey arrow.
No use of the final irreducible-extension clause is made. -/
theorem no_full_projection_and_local_trees
    {V : Type} [Finite V] (C : Structure language V)
    (hArrow : Arrow A B C (Fin 2))
    (p : V → Fin 3) (hp : C.IsHomomorphismEmbedding D p)
    (hLocal : LocallyClosedTreeCompletable B C 3) : False := by
  classical
  have hIrr : C.Irreducible := total_irreducible (total_of_full_projection hp.1)
  obtain ⟨eD, _⟩ := hp.2 C hIrr (Embedding.id C)
  letI : Fintype V := Fintype.ofFinite V
  have hSize : Fintype.card V ≤ 3 := by
    have h := Fintype.card_le_of_injective eD eD.injective
    simpa using h
  obtain ⟨Z, T, hTree, q, hq⟩ := hLocal.fullWitness hSize
  obtain ⟨eT, _⟩ := hq.2 C hIrr (Embedding.id C)
  obtain ⟨baseCopy, hContained⟩ :=
    hTree.irreducible_contained_in_copy hIrr eT
  let eB : Embedding C B := eT.factorThroughRange baseCopy hContained
  exact no_ramsey_with_embedding_into_two hArrow eB

/-- Negation of the exact published three-clause target. -/
theorem not_publishedSparseningConclusion :
    ¬ PublishedSparseningConclusion A B D (Fin 2) 3 := by
  rintro ⟨V, hV, C, hArrow, p, hp, hLocal, _hExtend⟩
  letI : Finite V := hV
  exact no_full_projection_and_local_trees C hArrow p hp hLocal

/-- Explicit nonvacuous counterexample, with irreducible A and B and only
a positive-arity, singleton-valued, total function. -/
theorem published_functional_counterexample :
    language.PositiveFuncArity ∧ A.Irreducible ∧ B.Irreducible ∧
    Arrow A B D (Fin 2) ∧
    ¬ PublishedSparseningConclusion A B D (Fin 2) 3 := by
  refine ⟨?_, total_irreducible (algebra_total _),
    total_irreducible (algebra_total _), three_ramsey_two,
    not_publishedSparseningConclusion⟩
  intro F
  decide

end StructuralRamsey.Structure.PublishedTotalBinaryObstruction
