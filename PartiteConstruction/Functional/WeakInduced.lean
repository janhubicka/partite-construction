import PartiteConstruction.Functional.Induced
import PartiteConstruction.Structure.WeakHomomorphism

/-! # The functional Partite Lemma needs only a weak projection

The Hales--Jewett line embeddings are full embeddings although the partition
projection need only preserve function incidences. Exactness of the line map
uses a parameter coordinate and output transversality of the power. This
avoids the much stronger, non-amalgamation-stable fibre-surjectivity hypothesis.
-/
namespace StructuralRamsey.FunctionalPartite.Induced

open Structure HalesJewett SuccessorTree

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- A letter sends every function value in B to the corresponding value in
its fixed transversal A-copy; only forward projection preservation is used. -/
theorem letter_func_member
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (e : Letter A B) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) {y : V} (hy : y ∈ B.func F x) :
    e (B.part y) ∈ B.func F (e ∘ (B.part ∘ x)) := by
  have hpart := hB.2 F x y hy
  have he := e.toEmbedding.map_func F (B.part ∘ x)
  rw [← he]
  exact ⟨B.part y, hpart, rfl⟩

theorem weak_lineMap_rel_iff
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W : Line (Letter A B) N) (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    (power B N).rel R (lineMap W ∘ x) ↔ B.rel R x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := W.hasParameter
    simpa only [lineMap, hi, Function.comp_apply] using h i
  · intro hx i
    cases hi : W.symbol i with
    | parameter =>
        simpa only [lineMap, hi, Function.comp_apply] using hx
    | const e =>
        have he0 := (e.toEmbedding.map_rel_iff R (B.part ∘ x)).mpr (hB.1 R x hx)
        let args : Fin (L.relArity R) → V := fun j => e (B.part (x j))
        have hargs : e ∘ (B.part ∘ x) = args := by funext j; rfl
        have he : B.rel R args := by rw [← hargs]; exact he0
        simpa only [args, lineMap, hi, Function.comp_apply] using he

theorem weak_lineMap_func_mem
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W : Line (Letter A B) N) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) {y : V} (hy : y ∈ B.func F x) :
    lineMap W y ∈ (power B N).func F (lineMap W ∘ x) := by
  intro i
  cases hi : W.symbol i with
  | parameter =>
      simpa only [lineMap, hi, Function.comp_apply] using hy
  | const e =>
      let args : Fin (L.funcArity F) → V := fun j => e (B.part (x j))
      have hargs : e ∘ (B.part ∘ x) = args := by funext j; rfl
      have he : e (B.part y) ∈ B.func F args := by
        rw [← hargs]
        exact letter_func_member hB e F x hy
      simpa only [args, lineMap, hi, Function.comp_apply] using he

/-- A single parameter coordinate supplies a preimage. Output transversality
of the power itself then proves equality, without a second coordinate chase. -/
theorem weak_lineMap_func
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W : Line (Letter A B) N) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    Structure.imageSet (lineMap W) (B.func F x) =
      (power B N).func F (lineMap W ∘ x) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact weak_lineMap_func_mem hB W F x hy
  · intro hz
    obtain ⟨i, hi⟩ := W.hasParameter
    have hy : z.coord i ∈ B.func F x := by
      simpa only [lineMap, hi, Function.comp_apply] using hz i
    refine ⟨z.coord i, hy, ?_⟩
    apply (power B N).funcTransversal F (lineMap W ∘ x)
      (lineMap W (z.coord i)) z (weak_lineMap_func_mem hB W F x hy) hz
    exact z.belongs i

def weak_lineEmbedding
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W : Line (Letter A B) N) :
    FunctionalPartite.Embedding B (power B N) where
  toFun := lineMap W
  injective := lineMap_injective W
  map_rel_iff := weak_lineMap_rel_iff hB W
  map_func := weak_lineMap_func hB W
  map_part := fun _ => rfl

def weak_wordEmbedding
    (hB : B.toStructure.IsWeakHomomorphism A B.part) (hN : 0 < N)
    (w : Fin N → Letter A B) :
    FunctionalPartite.Embedding (transversal A) (power B N) :=
  (weak_lineEmbedding hB (firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem weak_wordEmbedding_apply
    (hB : B.toStructure.IsWeakHomomorphism A B.part) (hN : 0 < N)
    (w : Fin N → Letter A B) (p : P) :
    weak_wordEmbedding hB hN w p = wordMap w p := by
  change lineMap (firstLine hN w) (w ⟨0, hN⟩ p) = _
  rw [lineMap_comp_letter, firstLine_eval]

theorem weak_lineEmbedding_comp_letter
    (hB : B.toStructure.IsWeakHomomorphism A B.part) (hN : 0 < N)
    (W : Line (Letter A B) N) (e : Letter A B) :
    (weak_lineEmbedding hB W).comp e = weak_wordEmbedding hB hN (W.eval e) := by
  apply FunctionalPartite.Embedding.ext
  intro p
  exact (lineMap_comp_letter W e p).trans
    (weak_wordEmbedding_apply hB hN (W.eval e) p).symm

/-- Functional Hales--Jewett Partite Lemma with only an EHN weak projection.
Every embedding in the Ramsey arrow is nevertheless a full embedding. -/
theorem weak_partiteLemma
    (hB : B.toStructure.IsWeakHomomorphism A B.part) [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧
      FunctionalPartite.Arrow (transversal A) B (power B N) κ := by
  classical
  letI : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (weak_wordEmbedding hB hN w))
  refine ⟨weak_lineEmbedding hB W, ?_⟩
  intro e₁ e₂
  simpa only [weak_lineEmbedding_comp_letter hB hN] using hW e₁ e₂

end StructuralRamsey.FunctionalPartite.Induced
