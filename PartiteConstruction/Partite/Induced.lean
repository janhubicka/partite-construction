import PartiteConstruction.Relational.Homomorphism
import PartiteConstruction.Partite.NonInduced

/-! # The induced Partite Lemma

The carrier of the power is the same tagged product used by the non-induced
construction. Here relations are interpreted coordinatewise. The projection
to the part structure is assumed to be a homomorphism-embedding; relation
preservation is the only part of that hypothesis needed for the Hales--Jewett
argument itself. The stronger projection invariant is verified separately.
-/
namespace StructuralRamsey.Partite

open RelStructure HalesJewett SuccessorTree

universe u v w

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- The survey's notion of an `A`-partite system: the partition projection
is a homomorphism-embedding of the relational reduct to `A`. -/
def System.IsPartiteOver (B : System L P V) (A : RelStructure L P) : Prop :=
  B.toRelStructure.IsHomomorphismEmbedding A B.part

namespace Induced

variable (A : RelStructure L P) (B : System L P V)

abbrev Letter := NonInduced.Letter A B
abbrev Vertex (N : ℕ) := NonInduced.Vertex B N

variable {A B} {N : ℕ}

/-- Coordinatewise power from the induced partite construction. -/
def power (B : System L P V) (N : ℕ) : System L P (Vertex B N) where
  part := NonInduced.Vertex.part
  rel R z := ∀ i, B.rel R (fun j => (z j).coord i)
  transversal := by
    intro R z hz i j hp
    apply NonInduced.Vertex.ext B hp
    intro k
    apply B.transversal R (fun t => (z t).coord k) (hz k) i j
    exact ((z i).belongs k).trans (hp.trans ((z j).belongs k).symm)

/-- For a positive power, its projection preserves all relations. Positivity
is essential: at exponent zero the coordinatewise relation condition is
vacuous. -/
theorem power_projection_homomorphism (hB : B.IsPartiteOver A) (hN : 0 < N) :
    (power B N).toRelStructure.IsHomomorphism A (power B N).part := by
  intro R z hz
  let i0 : Fin N := ⟨0, hN⟩
  have hcoord : B.rel R (fun j => (z j).coord i0) := hz i0
  have hA := hB.1 R (fun j => (z j).coord i0) hcoord
  convert hA using 1
  funext j
  exact ((z j).belongs i0).symm

/-- Reflection for each Hales--Jewett line is immediate from a parameter
coordinate; preservation at constant coordinates uses the projection
homomorphism and the letter embedding. -/
theorem lineMap_rel_iff (hB : B.IsPartiteOver A)
    (W : Line (Letter A B) N) (R : L.Symbol)
    (x : Fin (L.arity R) → V) :
    (power B N).rel R (NonInduced.lineMap W ∘ x) ↔ B.rel R x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := W.hasParameter
    have hiRel := h i
    simpa only [NonInduced.lineMap, hi, Function.comp_apply] using hiRel
  · intro hx i
    cases hi : W.symbol i with
    | parameter =>
        simpa only [NonInduced.lineMap, hi, Function.comp_apply] using hx
    | const e =>
        have hA : A.rel R (B.part ∘ x) := hB.1 R x hx
        have he : B.rel R (e ∘ (B.part ∘ x)) :=
          (e.toEmbedding.map_rel_iff R (B.part ∘ x)).mpr hA
        change B.rel R (fun j => e (B.part (x j)))
        convert he using 1

/-- Every parameter word gives an induced part-preserving embedding into the
coordinatewise power. -/
def lineEmbedding (hB : B.IsPartiteOver A) (W : Line (Letter A B) N) :
    Partite.Embedding B (power B N) where
  toFun := NonInduced.lineMap W
  injective := NonInduced.lineMap_injective W
  map_rel_iff := lineMap_rel_iff hB W
  map_part := fun _ => rfl

/-- Word embedding into the coordinatewise power. -/
def wordEmbedding (hB : B.IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Letter A B) :
    Partite.Embedding (transversal A) (power B N) :=
  (lineEmbedding hB (NonInduced.firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem wordEmbedding_apply (hB : B.IsPartiteOver A) (hN : 0 < N)
    (w : Fin N → Letter A B) (p : P) :
    wordEmbedding hB hN w p = NonInduced.wordMap w p := by
  change NonInduced.lineMap (NonInduced.firstLine hN w) (w ⟨0, hN⟩ p) = _
  rw [NonInduced.lineMap_comp_letter, NonInduced.firstLine_eval]

theorem lineEmbedding_comp_letter (hB : B.IsPartiteOver A) (hN : 0 < N)
    (W : Line (Letter A B) N) (e : Letter A B) :
    (lineEmbedding hB W).comp e = wordEmbedding hB hN (W.eval e) := by
  apply Partite.Embedding.ext
  intro p
  exact (NonInduced.lineMap_comp_letter W e p).trans
    (wordEmbedding_apply hB hN (W.eval e) p).symm

/-- Induced Partite Lemma for any finite colour type. -/
theorem partiteLemma (hB : B.IsPartiteOver A) [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ Partite.Arrow (transversal A) B (power B N) κ := by
  classical
  let : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ := HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hHJ (fun w => χ (wordEmbedding hB hN w))
  refine ⟨lineEmbedding hB W, ?_⟩
  intro e₁ e₂
  simpa only [lineEmbedding_comp_letter hB hN] using hW e₁ e₂

end Induced
end StructuralRamsey.Partite
