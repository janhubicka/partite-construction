import PartiteConstruction.Functional.Basic
import PartiteConstruction.HalesJewett.Finite

/-! # Induced Partite Lemma with relations and set-valued functions

The coordinatewise power is valid for genuinely set-valued functions provided
function values are transversal across the parts.  This is the direct
functional analogue of the U-transversality invariant used after relational
encoding in the recursive construction.
-/
namespace StructuralRamsey.FunctionalPartite.Induced

open Structure HalesJewett SuccessorTree

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable (A : Structure L P) (B : System L P V)

abbrev Letter := FunctionalPartite.Embedding (transversal A) B

structure Vertex (N : ℕ) where
  part : P
  coord : Fin N → V
  belongs : ∀ i, B.part (coord i) = part

namespace Vertex

@[ext] theorem ext {N} {x y : Vertex B N}
    (hp : x.part = y.part) (hc : ∀ i, x.coord i = y.coord i) : x = y := by
  cases x; cases y
  simp_all only [mk.injEq]
  exact ⟨trivial, funext hc⟩

instance {N} [Finite P] [Finite V] : Finite (Vertex B N) :=
  Finite.of_injective (fun x => (x.part, x.coord)) (by
    intro x y h
    exact ext B (congrArg Prod.fst h) (congrFun (congrArg Prod.snd h)))

end Vertex

variable {A B} {N : ℕ}

def lineMap (W : Line (Letter A B) N) (x : V) : Vertex B N where
  part := B.part x
  coord i := match W.symbol i with
    | .const e => e (B.part x)
    | .parameter => x
  belongs i := by
    cases h : W.symbol i with
    | const e => exact e.map_part (B.part x)
    | parameter => rfl

theorem lineMap_injective (W : Line (Letter A B) N) :
    Function.Injective (lineMap W) := by
  obtain ⟨i, hi⟩ := W.hasParameter
  intro x y h
  have hc := congrArg (fun v => v.coord i) h
  simpa only [lineMap, hi] using hc

/-- Coordinatewise power for both relations and set-valued functions. -/
def power (B : System L P V) (N : ℕ) : System L P (Vertex B N) where
  part := Vertex.part
  rel R z := ∀ i, B.rel R (fun j => (z j).coord i)
  func F x := {y | ∀ i, y.coord i ∈ B.func F (fun j => (x j).coord i)}
  relTransversal := by
    intro R z hz i j hp
    apply Vertex.ext B hp
    intro k
    apply B.relTransversal R (fun t => (z t).coord k) (hz k) i j
    exact ((z i).belongs k).trans (hp.trans ((z j).belongs k).symm)
  funcTransversal := by
    intro F x y z hy hz hp
    apply Vertex.ext B hp
    intro k
    apply B.funcTransversal F (fun j => (x j).coord k)
      (y.coord k) (z.coord k) (hy k) (hz k)
    exact (y.belongs k).trans (hp.trans (z.belongs k).symm)

/-- Positive coordinate powers retain the full projection homomorphism,
including equality of set-valued function images. -/
theorem power_projectionHom
    (hB : B.ProjectionHom A) (hN : 0 < N) :
    (power B N).ProjectionHom A := by
  constructor
  · intro R z hz
    let i0 : Fin N := ⟨0, hN⟩
    have hcoord : B.rel R (fun j => (z j).coord i0) := hz i0
    have hA := hB.1 R (fun j => (z j).coord i0) hcoord
    convert hA using 1
    funext j
    exact ((z j).belongs i0).symm
  · intro F x
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      let i0 : Fin N := ⟨0, hN⟩
      have hcoord : y.coord i0 ∈
          B.func F (fun j => (x j).coord i0) := hy i0
      have himg :
          B.part (y.coord i0) ∈
            Structure.imageSet B.part
              (B.func F (fun j => (x j).coord i0)) :=
        ⟨y.coord i0, hcoord, rfl⟩
      rw [hB.2 F (fun j => (x j).coord i0)] at himg
      have heq :
          B.part ∘ (fun j => (x j).coord i0) =
            (power B N).part ∘ x := by
        funext j
        exact (x j).belongs i0
      rw [heq, y.belongs i0] at himg
      exact himg
    · intro ha
      have hex : ∀ i : Fin N,
          ∃ b : V,
            b ∈ B.func F (fun j => (x j).coord i) ∧
            B.part b = a := by
        intro i
        have heq :
            B.part ∘ (fun j => (x j).coord i) =
              (power B N).part ∘ x := by
          funext j
          exact (x j).belongs i
        have hai : a ∈
            A.func F (B.part ∘ (fun j => (x j).coord i)) := by
          rw [heq]
          exact ha
        rw [← hB.2 F (fun j => (x j).coord i)] at hai
        rcases hai with ⟨b, hb, hba⟩
        exact ⟨b, hb, hba⟩
      choose b hb hpart using hex
      let y : Vertex B N := {
        part := a
        coord := b
        belongs := hpart
      }
      refine ⟨y, ?_, rfl⟩
      exact hb

theorem lineMap_rel_iff
    (hB : B.ProjectionHom A)
    (W : Line (Letter A B) N) (R : L.RelSymbol)
    (x : Fin (L.relArity R) → V) :
    (power B N).rel R (lineMap W ∘ x) ↔ B.rel R x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := W.hasParameter
    have hiRel := h i
    simpa only [lineMap, hi, Function.comp_apply] using hiRel
  · intro hx i
    cases hi : W.symbol i with
    | parameter =>
        simpa only [lineMap, hi, Function.comp_apply] using hx
    | const e =>
        have hA : A.rel R (B.part ∘ x) := hB.1 R x hx
        have he0 : B.rel R (e ∘ (B.part ∘ x)) :=
          (e.toEmbedding.map_rel_iff R (B.part ∘ x)).mpr hA
        let args : Fin (L.relArity R) → V :=
          fun j => e (B.part (x j))
        have hargs : (e ∘ (B.part ∘ x)) = args := by
          funext j
          rfl
        have he : B.rel R args := by
          rw [← hargs]
          exact he0
        simpa only [args, lineMap, hi, Function.comp_apply] using he

/-- Exact preservation of set-valued function images by a Hales--Jewett line.
A parameter coordinate supplies a preimage; output transversality of the
whole power supplies uniqueness, without repeating the coordinate analysis. -/
theorem lineMap_func
    (hB : B.ProjectionHom A)
    (W : Line (Letter A B) N) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    Structure.imageSet (lineMap W) (B.func F x) =
      (power B N).func F (lineMap W ∘ x) := by
  have hmem {y : V} (hy : y ∈ B.func F x) :
      lineMap W y ∈ (power B N).func F (lineMap W ∘ x) := by
    intro i
    cases hi : W.symbol i with
    | parameter =>
        simpa only [lineMap, hi, Function.comp_apply] using hy
    | const e =>
        have hpartValue : B.part y ∈ A.func F (B.part ∘ x) := by
          have himg : B.part y ∈ Structure.imageSet B.part (B.func F x) :=
            ⟨y, hy, rfl⟩
          rw [hB.2 F x] at himg
          exact himg
        let args : Fin (L.funcArity F) → V := fun j => e (B.part (x j))
        have hargs : e ∘ (B.part ∘ x) = args := by funext j; rfl
        have heValue : e (B.part y) ∈ B.func F args := by
          have himg : e (B.part y) ∈ Structure.imageSet e (A.func F (B.part ∘ x)) :=
            ⟨B.part y, hpartValue, rfl⟩
          have hm := e.toEmbedding.map_func F (B.part ∘ x)
          change Structure.imageSet e (A.func F (B.part ∘ x)) =
              B.func F (e ∘ (B.part ∘ x)) at hm
          rw [hm, hargs] at himg
          exact himg
        simpa only [args, lineMap, hi, Function.comp_apply] using heValue
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hmem hy
  · intro hz
    obtain ⟨i, hi⟩ := W.hasParameter
    have hy : z.coord i ∈ B.func F x := by
      simpa only [lineMap, hi, Function.comp_apply] using hz i
    refine ⟨z.coord i, hy, ?_⟩
    apply (power B N).funcTransversal F (lineMap W ∘ x)
      (lineMap W (z.coord i)) z (hmem hy) hz
    exact z.belongs i

def lineEmbedding
    (hB : B.ProjectionHom A) (W : Line (Letter A B) N) :
    FunctionalPartite.Embedding B (power B N) where
  toFun := lineMap W
  injective := lineMap_injective W
  map_rel_iff := lineMap_rel_iff hB W
  map_func := lineMap_func hB W
  map_part := fun _ => rfl

def wordMap (w : Fin N → Letter A B) (p : P) : Vertex B N where
  part := p
  coord i := w i p
  belongs i := (w i).map_part p

theorem lineMap_comp_letter
    (W : Line (Letter A B) N) (e : Letter A B) (p : P) :
    lineMap W (e p) = wordMap (W.eval e) p := by
  apply Vertex.ext
  · exact e.map_part p
  · intro i
    cases h : W.symbol i with
    | parameter => simp only [lineMap, h, wordMap, Line.eval, LineSymbol.eval]
    | const d =>
        simp only [lineMap, h, wordMap, Line.eval, LineSymbol.eval, e.map_part p]
        rfl

def firstLine (hN : 0 < N) (w : Fin N → Letter A B) :
    Line (Letter A B) N where
  symbol i := if i = ⟨0, hN⟩ then .parameter else .const (w i)
  hasParameter := ⟨⟨0, hN⟩, by simp⟩

@[simp] theorem firstLine_eval (hN : 0 < N) (w : Fin N → Letter A B) :
    (firstLine hN w).eval (w ⟨0, hN⟩) = w := by
  funext i
  by_cases hi : i = ⟨0, hN⟩
  · subst i
    simp [firstLine, Line.eval, LineSymbol.eval]
  · simp [firstLine, Line.eval, LineSymbol.eval, hi]

def wordEmbedding
    (hB : B.ProjectionHom A) (hN : 0 < N)
    (w : Fin N → Letter A B) :
    FunctionalPartite.Embedding (transversal A) (power B N) :=
  (lineEmbedding hB (firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem wordEmbedding_apply
    (hB : B.ProjectionHom A) (hN : 0 < N)
    (w : Fin N → Letter A B) (p : P) :
    wordEmbedding hB hN w p = wordMap w p := by
  change lineMap (firstLine hN w) (w ⟨0, hN⟩ p) = _
  rw [lineMap_comp_letter, firstLine_eval]

theorem lineEmbedding_comp_letter
    (hB : B.ProjectionHom A) (hN : 0 < N)
    (W : Line (Letter A B) N) (e : Letter A B) :
    (lineEmbedding hB W).comp e = wordEmbedding hB hN (W.eval e) := by
  apply FunctionalPartite.Embedding.ext
  intro p
  exact (lineMap_comp_letter W e p).trans
    (wordEmbedding_apply hB hN (W.eval e) p).symm

/-- Induced Partite Lemma for relation/function structures with set-valued
functions. -/
theorem partiteLemma
    (hB : B.ProjectionHom A) [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧
      FunctionalPartite.Arrow (transversal A) B (power B N) κ := by
  classical
  letI : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordEmbedding hB hN w))
  refine ⟨lineEmbedding hB W, ?_⟩
  intro e₁ e₂
  simpa only [lineEmbedding_comp_letter hB hN] using hW e₁ e₂

end StructuralRamsey.FunctionalPartite.Induced
