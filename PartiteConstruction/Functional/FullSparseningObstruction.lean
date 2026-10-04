import PartiteConstruction.Structure.Order
import PartiteConstruction.Functional.WeakOperations

/-! # The literal full-function sparsening statement is false

The sparsening theorem used in the Hubicka--Nesetril construction is a
relational theorem.  If it is stated directly for function languages using
this repository's survey homomorphisms (which map each set-valued function
fibre *onto* the target fibre), properties (1) and (3) already conflict with
the Ramsey arrow for a very small example.

Take one binary function interpreted as first projection.  Let A be the
one-point ordered structure and B the two-point ordered structure.  The
three-point ordered structure C0 is a Ramsey witness for colouring A-copies:
three vertices coloured with two colours contain a monochromatic ordered
pair.  But any C admitting a full function homomorphism into C0 has the binary
function defined at every input.  Such a C is irreducible.  Property (3) would
therefore put all of C inside one B-copy, so C is isomorphic to B; B itself is
not Ramsey for A and two colours.

This is independent of the weak-substructure issue.  It shows that the direct
function-language version of the sparsening theorem must not use the survey's
fibre-surjective homomorphism.  The clean source-faithful statement is
relational; functions can be handled later by an appropriate relational
encoding.
-/

namespace StructuralRamsey.Structure.FullFunctionalSparseningObstruction

open StructuralRamsey

def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 2

/-- Binary first projection on an arbitrary carrier. -/
def projStructure (X : Type) : Structure language X where
  rel R := Empty.elim R
  func F x := by
    cases F
    exact {y | y = x (0 : Fin 2)}

abbrev A0 := projStructure (Fin 1)
abbrev B0 := projStructure (Fin 2)
abbrev C00 := projStructure (Fin 3)

abbrev A := A0.withLinearOrder
abbrev B := B0.withLinearOrder
abbrev C0 := C00.withLinearOrder

theorem positiveArity : language.PositiveFuncArity := by
  intro F
  exact Nat.zero_lt_succ 1

/-- Every strictly increasing map gives an embedding of projection structures
with their canonical orders. -/
def orderedEmbedding
    {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) :
    Embedding (projStructure (Fin m)).withLinearOrder
      (projStructure (Fin n)).withLinearOrder where
  toFun := f
  injective := hf.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact Empty.elim R
    | inr _ => exact hf.lt_iff_lt
  map_func := by
    intro F x
    cases F
    change
      imageSet f {z | z = x (0 : Fin 2)} =
        {z | z = (f ∘ x) (0 : Fin 2)}
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      subst z
      rfl
    · intro hy
      change y = f (x (0 : Fin 2)) at hy
      subst y
      exact ⟨x (0 : Fin 2), rfl, rfl⟩

def singletonMap (i : Fin 3) : Fin 1 → Fin 3 := fun _ => i

theorem singletonMap_strict (i : Fin 3) : StrictMono (singletonMap i) := by
  intro a b hab
  omega

def singletonEmbedding (i : Fin 3) : Embedding A C0 :=
  orderedEmbedding (singletonMap i) (singletonMap_strict i)

def pairMap (i j : Fin 3) : Fin 2 → Fin 3 :=
  fun k => Fin.cases i (fun _ => j) k

theorem pairMap_strict {i j : Fin 3} (hij : i < j) :
    StrictMono (pairMap i j) := by
  intro a b hab
  have ha : a = 0 := by omega
  have hb : b = 1 := by omega
  subst a
  subst b
  change i < j
  exact hij

def pairEmbedding (i j : Fin 3) (hij : i < j) : Embedding B C0 :=
  orderedEmbedding (pairMap i j) (pairMap_strict hij)

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  omega

theorem singleton_comp_pair
    (i j : Fin 3) (hij : i < j)
    (e : Embedding A B) :
    (pairEmbedding i j hij).comp e =
      singletonEmbedding ((pairEmbedding i j hij) (e 0)) := by
  apply Embedding.ext
  intro x
  have hx : x = 0 := by omega
  subst x
  rfl

theorem pair_monochromatic
    (χ : Embedding A C0 → Bool)
    (i j : Fin 3) (hij : i < j)
    (hχ : χ (singletonEmbedding i) = χ (singletonEmbedding j)) :
    ∀ e₁ e₂ : Embedding A B,
      χ ((pairEmbedding i j hij).comp e₁) =
        χ ((pairEmbedding i j hij).comp e₂) := by
  intro e₁ e₂
  rw [singleton_comp_pair, singleton_comp_pair]
  have hp0 : (pairEmbedding i j hij) (0 : Fin 2) = i := rfl
  have hp1 : (pairEmbedding i j hij) (1 : Fin 2) = j := rfl
  rcases fin2_cases (e₁ 0) with h10 | h11
  <;> rcases fin2_cases (e₂ 0) with h20 | h21
  · rw [h10, h20, hp0]
  · rw [h10, h21, hp0, hp1]
    exact hχ
  · rw [h11, h20, hp0, hp1]
    exact hχ.symm
  · rw [h11, h21, hp1]

/-- The explicit three-point target is Ramsey for one-point A and two-point B. -/
theorem target_ramsey : Arrow A B C0 Bool := by
  intro χ
  by_cases h01 :
      χ (singletonEmbedding 0) = χ (singletonEmbedding 1)
  · exact ⟨pairEmbedding 0 1 (by decide),
      pair_monochromatic χ 0 1 (by decide) h01⟩
  by_cases h02 :
      χ (singletonEmbedding 0) = χ (singletonEmbedding 2)
  · exact ⟨pairEmbedding 0 2 (by decide),
      pair_monochromatic χ 0 2 (by decide) h02⟩
  have h12 :
      χ (singletonEmbedding 1) = χ (singletonEmbedding 2) := by
    cases h0 : χ (singletonEmbedding 0)
    <;> cases h1 : χ (singletonEmbedding 1)
    <;> cases h2 : χ (singletonEmbedding 2)
    <;> simp_all
  exact ⟨pairEmbedding 1 2 (by decide),
    pair_monochromatic χ 1 2 (by decide) h12⟩

/-- A structure whose distinguished binary function is nonempty at every input
is irreducible. -/
theorem irreducible_of_total_binary
    {X : Type} (C : Structure language.withLinearOrder X)
    (htotal : ∀ x : Fin 2 → X, ∃ y, y ∈ C.func () x) :
    C.Irreducible := by
  intro H E F Z Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  by_cases hE : ∀ a : X, ∃ x : E, e a = iE x
  · exact Or.inl hE
  by_cases hF : ∀ a : X, ∃ x : F, e a = iF x
  · exact Or.inr hF
  push Not at hE hF
  obtain ⟨a, ha⟩ := hE
  obtain ⟨b, hb⟩ := hF
  exfalso
  let args : Fin 2 → X := ![a, b]
  obtain ⟨y, hy⟩ := htotal args
  have hey : e y ∈ Csrc.func () (e ∘ args) := by
    have himg : e y ∈ imageSet e (C.func () args) := ⟨y, hy, rfl⟩
    rw [e.map_func () args] at himg
    exact himg
  rcases (hfree.func_iff () (e ∘ args) (e y)).mp hey with
    hleft | hright
  · rcases hleft with ⟨q, z, hz, hargs, hout⟩
    change Fin 2 → E at q
    apply ha (q (0 : Fin 2))
    have h := congrFun hargs (0 : Fin 2)
    simpa [args, Function.comp_apply] using h
  · rcases hright with ⟨q, z, hz, hargs, hout⟩
    change Fin 2 → F at q
    apply hb (q (1 : Fin 2))
    have h := congrFun hargs (1 : Fin 2)
    simpa [args, Function.comp_apply] using h

theorem A_irreducible : A.Irreducible := by
  intro H E F Z Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  rcases hfree.covers (e 0) with ⟨x, hx⟩ | ⟨x, hx⟩
  · refine Or.inl ?_
    intro a
    have ha : a = 0 := by omega
    subst a
    exact ⟨x, hx⟩
  · refine Or.inr ?_
    intro a
    have ha : a = 0 := by omega
    subst a
    exact ⟨x, hx⟩

theorem B_total :
    ∀ x : Fin 2 → Fin 2, ∃ y, y ∈ B.func () x := by
  intro x
  refine ⟨x 0, ?_⟩
  simp [B, B0, projStructure, Structure.withLinearOrder]

theorem B_irreducible : B.Irreducible :=
  irreducible_of_total_binary B B_total

/-- B itself is not Ramsey for A and two colours. -/
theorem B_not_ramsey : ¬ Arrow A B B Bool := by
  intro h
  let χ : Embedding A B → Bool :=
    fun e => decide ((e 0).val = 1)
  obtain ⟨f, hf⟩ := h χ
  let e0 : Embedding A B :=
    orderedEmbedding (fun _ : Fin 1 => (0 : Fin 2))
      (by intro a b hab; omega)
  let e1 : Embedding A B :=
    orderedEmbedding (fun _ : Fin 1 => (1 : Fin 2))
      (by intro a b hab; omega)
  have hmono := hf e0 e1
  have hne : f (0 : Fin 2) ≠ f (1 : Fin 2) := by
    intro heq
    have h01 : (0 : Fin 2) = 1 := f.injective heq
    omega
  rcases fin2_cases (f 0) with h00 | h01
  <;> rcases fin2_cases (f 1) with h10 | h11
  <;> simp_all [χ, e0, e1, orderedEmbedding]

/-- If C maps by a full homomorphism to the total projection target C0, then C
itself has a nonempty binary fibre at every input. -/
theorem total_of_full_projection
    {X : Type} (C : Structure language.withLinearOrder X)
    {p : X → Fin 3}
    (hp : C.IsHomomorphism C0 p) :
    ∀ x : Fin 2 → X, ∃ y, y ∈ C.func () x := by
  intro x
  have ht :
      p (x 0) ∈ C0.func () (p ∘ x) := by
    simp [C0, C00, projStructure, Structure.withLinearOrder]
    rfl
  have himg :
      p (x 0) ∈ imageSet p (C.func () x) := by
    rw [hp.2 () x]
    exact ht
  rcases himg with ⟨y, hy, _⟩
  exact ⟨y, hy⟩

/-- A surjective B-copy lets Ramsey arrows on C descend back to B. -/
theorem arrow_descends_surjective
    {X : Type} (C : Structure language.withLinearOrder X)
    (hC : Arrow A B C Bool)
    (g : Embedding B C) (hgsurj : Function.Surjective g) :
    Arrow A B B Bool := by
  let r : Embedding C B :=
    (Embedding.id C).factorThroughClosedRange g
      (fun x => by
        obtain ⟨b, hb⟩ := hgsurj x
        exact ⟨b, hb.symm⟩)
  intro χ
  obtain ⟨f, hf⟩ := hC (fun e => χ (r.comp e))
  refine ⟨r.comp f, ?_⟩
  intro e₁ e₂
  have h1 : (r.comp f).comp e₁ = r.comp (f.comp e₁) := by
    apply Embedding.ext
    intro x
    rfl
  have h2 : (r.comp f).comp e₂ = r.comp (f.comp e₂) := by
    apply Embedding.ext
    intro x
    rfl
  rw [h1, h2]
  exact hf e₁ e₂

/-- No structure can simultaneously have the Ramsey arrow, a full
homomorphism-embedding to the explicit target C0, and the whole-structure
consequence of property (3). -/
theorem no_sparse_witness :
    ¬ ∃ (X : Type) (C : Structure language.withLinearOrder X),
      Arrow A B C Bool ∧
      (∃ p : X → Fin 3, C.IsHomomorphismEmbedding C0 p) ∧
      (C.Irreducible → ∃ g : Embedding B C, Function.Surjective g) := by
  rintro ⟨X, C, hArrow, ⟨p, hp⟩, hcover⟩
  have htotal : ∀ x : Fin 2 → X, ∃ y, y ∈ C.func () x :=
    total_of_full_projection C hp.1
  have hCirr : C.Irreducible :=
    irreducible_of_total_binary C htotal
  obtain ⟨g, hgsurj⟩ := hcover hCirr
  exact B_not_ramsey (arrow_descends_surjective C hArrow g hgsurj)

/-- The explicit target satisfies the theorem's Ramsey hypothesis, while no
output can satisfy even the weakened whole-structure form of properties
(1) and (3). -/
theorem direct_functional_sparsening_false :
    Arrow A B C0 Bool ∧ A.Irreducible ∧ B.Irreducible ∧
      ¬ ∃ (X : Type) (C : Structure language.withLinearOrder X),
        Arrow A B C Bool ∧
        (∃ p : X → Fin 3, C.IsHomomorphismEmbedding C0 p) ∧
        (C.Irreducible → ∃ g : Embedding B C, Function.Surjective g) :=
  ⟨target_ramsey, A_irreducible, B_irreducible, no_sparse_witness⟩

end StructuralRamsey.Structure.FullFunctionalSparseningObstruction
