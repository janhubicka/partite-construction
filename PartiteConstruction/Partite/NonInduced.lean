import PartiteConstruction.Partite.Basic
import PartiteConstruction.Partite.Predicates
import PartiteConstruction.HalesJewett.Finite

/-! # The non-induced Partite Lemma

Relations in the power are the union of images under ALL parameter-word maps,
not the coordinatewise product. Reflection of relations is the main obligation.
The term “non-induced” names the construction; all embeddings here are induced.
-/
namespace StructuralRamsey.Partite.NonInduced

open RelStructure HalesJewett SuccessorTree

universe u v w
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}
variable (A : RelStructure L P) (B : System L P V)

abbrev Letter := Partite.Embedding (transversal A) B

/-- A tagged power of a part; the tag avoids any reliance on inhabited parts. -/
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

/-- The parameter-word map `f_W` from the survey. -/
def lineMap (W : Line (Letter A B) N) (x : V) : Vertex B N where
  part := B.part x
  coord i := match W.symbol i with
    | .const e => e (B.part x)
    | .parameter => x
  belongs i := by
    cases h : W.symbol i with
    | const e => exact e.map_part (B.part x)
    | parameter => rfl

@[simp] theorem lineMap_part (W : Line (Letter A B) N) (x : V) :
    (lineMap W x).part = B.part x := rfl

theorem lineMap_injective (W : Line (Letter A B) N) :
    Function.Injective (lineMap W) := by
  obtain ⟨i, hi⟩ := W.hasParameter
  intro x y h
  have := congrArg (fun v => v.coord i) h
  simpa only [lineMap, hi] using this

/-- The union-of-line-images relation, exactly as in Appendix A. -/
def power (A : RelStructure L P) (B : System L P V) (N : ℕ) : System L P (Vertex B N) where
  part := Vertex.part
  rel R z := ∃ (W : Line (Letter A B) N) (x : Fin (L.arity R) → V),
    B.rel R x ∧ z = lineMap W ∘ x
  transversal := by
    intro R z hz i j hp
    obtain ⟨W, x, hx, rfl⟩ := hz
    exact congrArg (lineMap W) (B.transversal R x hx i j hp)

/-- Main reflection argument: two line images cannot create a new relation
inside either image, even when their variable positions are disjoint. -/
theorem lineMap_rel_iff (W : Line (Letter A B) N) (R : L.Symbol)
    (x : Fin (L.arity R) → V) :
    (power A B N).rel R (lineMap W ∘ x) ↔ B.rel R x := by
  constructor
  · rintro ⟨W', y, hy, heq⟩
    have parts : ∀ k, B.part (x k) = B.part (y k) :=
      fun k => congrArg Vertex.part (congrFun heq k)
    have coords : ∀ k i, (lineMap W (x k)).coord i = (lineMap W' (y k)).coord i :=
      fun k i => congrArg (fun z => z.coord i) (congrFun heq k)
    obtain ⟨i, hi⟩ := W.hasParameter
    obtain ⟨j, hj⟩ := W'.hasParameter
    cases h'i : W'.symbol i with
    | parameter =>
        have hxy : x = y := by
          funext k
          simpa only [lineMap, hi, h'i] using coords k i
        simpa only [hxy] using hy
    | const e =>
        have hx : x = e ∘ (B.part ∘ y) := by
          funext k
          simpa only [lineMap, hi, h'i, Function.comp_apply] using coords k i
        cases hwj : W.symbol j with
        | parameter =>
            have hxy : x = y := by
              funext k
              simpa only [lineMap, hwj, hj] using coords k j
            simpa only [hxy] using hy
        | const d =>
            have hyd : d ∘ (B.part ∘ y) = y := by
              funext k
              simpa only [lineMap, hwj, hj, Function.comp_apply, parts k] using coords k j
            have hA : A.rel R (B.part ∘ y) :=
              (d.map_rel_iff R (B.part ∘ y)).mp (by simpa only [hyd] using hy)
            rw [hx]
            exact (e.map_rel_iff R (B.part ∘ y)).mpr hA
  · intro hx
    exact ⟨W, x, hx, rfl⟩

/-- Claim `clm1`: every parameter word gives an induced part-preserving embedding. -/
def lineEmbedding (W : Line (Letter A B) N) : Partite.Embedding B (power A B N) where
  toFun := lineMap W
  injective := lineMap_injective W
  map_rel_iff := lineMap_rel_iff W
  map_part := fun _ => rfl

/-- The word map `e_w` from the survey. -/
def wordMap (w : Fin N → Letter A B) (p : P) : Vertex B N where
  part := p
  coord i := w i p
  belongs i := (w i).map_part p

/-- Claim `clm3`, the substitution identity. -/
theorem lineMap_comp_letter (W : Line (Letter A B) N) (e : Letter A B) (p : P) :
    lineMap W (e p) = wordMap (W.eval e) p := by
  apply Vertex.ext
  · exact e.map_part p
  · intro i
    cases h : W.symbol i with
    | parameter => simp only [lineMap, h, wordMap, Line.eval, LineSymbol.eval]
    | const d =>
        simp only [lineMap, h, wordMap, Line.eval, LineSymbol.eval, e.map_part p]
        rfl

/-- Every nonempty word lies on a parameter line: replace its first letter by
the parameter. This also makes explicit why a positive HJ length is needed. -/
def firstLine (hN : 0 < N) (w : Fin N → Letter A B) : Line (Letter A B) N where
  symbol i := if i = ⟨0, hN⟩ then .parameter else .const (w i)
  hasParameter := ⟨⟨0, hN⟩, by simp⟩

@[simp] theorem firstLine_eval (hN : 0 < N) (w : Fin N → Letter A B) :
    (firstLine hN w).eval (w ⟨0, hN⟩) = w := by
  funext i
  by_cases hi : i = ⟨0, hN⟩
  · subst i; simp [firstLine, Line.eval, LineSymbol.eval]
  · simp [firstLine, Line.eval, LineSymbol.eval, hi]

/-- The induced embedding corresponding to a word, constructed by composition. -/
def wordEmbedding (hN : 0 < N) (w : Fin N → Letter A B) :
    Partite.Embedding (transversal A) (power A B N) :=
  (lineEmbedding (firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem wordEmbedding_apply (hN : 0 < N) (w : Fin N → Letter A B) (p : P) :
    wordEmbedding hN w p = wordMap w p := by
  change lineMap (firstLine hN w) (w ⟨0, hN⟩ p) = _
  rw [lineMap_comp_letter, firstLine_eval]

theorem lineEmbedding_comp_letter (hN : 0 < N) (W : Line (Letter A B) N)
    (e : Letter A B) :
    (lineEmbedding W).comp e = wordEmbedding hN (W.eval e) := by
  apply Partite.Embedding.ext
  intro p
  exact (lineMap_comp_letter W e p).trans (wordEmbedding_apply hN (W.eval e) p).symm

/-- Finite non-induced Partite Lemma, for any finite colour type. The size N
depends only on A, B and the colour type, never on the colouring. -/
theorem partiteLemma [Finite P] [Finite V] (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ Partite.Arrow (transversal A) B (power A B N) κ := by
  classical
  let : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordEmbedding hN w))
  refine ⟨lineEmbedding W, ?_⟩
  intro e₁ e₂
  simpa only [lineEmbedding_comp_letter hN] using hW e₁ e₂

/-- The same finite witness expressed using ordinary structural Ramsey arrows
in the expanded language. This is the exact unary-predicate interface. -/
theorem partiteLemma_expanded [Finite P] [Finite V] (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ StructuralRamsey.Arrow (transversal A).expand B.expand
      (power A B N).expand κ := by
  obtain ⟨N, hN, h⟩ := partiteLemma (A := A) (B := B) κ
  exact ⟨N, hN, arrow_iff_expanded.mp h⟩

end StructuralRamsey.Partite.NonInduced
