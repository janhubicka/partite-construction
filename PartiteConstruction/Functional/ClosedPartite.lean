import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Induced
import PartiteConstruction.HalesJewett.Finite

/-! # Induced Partite Lemma with U-closed embeddings

This is the relational-graph version used for genuine set-valued functions.
The Hales--Jewett alphabet consists of U-closed partite embeddings, the
coordinate power preserves U-transversality, and every line/word map is
U-closed.
-/
namespace StructuralRamsey.Partite.Closed

open RelStructure HalesJewett SuccessorTree Structure

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Partite embeddings whose underlying relational embedding is U-closed. -/
def Embedding (A : Partite.System L.graph P V)
    (B : Partite.System L.graph P W) :=
  {e : Partite.Embedding A B //
    RelStructure.FunctionClosedMap
      A.toRelStructure B.toRelStructure e}

instance {A : Partite.System L.graph P V}
    {B : Partite.System L.graph P W} :
    CoeFun (Embedding A B) (fun _ => V → W) :=
  ⟨fun e => e.1⟩

namespace Embedding

variable {A : Partite.System L.graph P V}
  {B : Partite.System L.graph P W}

def id (A : Partite.System L.graph P V) : Embedding A A :=
  ⟨Partite.Embedding.id A, by
    intro F x y hy
    exact ⟨y, hy, rfl⟩⟩

def comp {X : Type v} {C : Partite.System L.graph P X}
    (g : Embedding B C) (f : Embedding A B) :
    Embedding A C :=
  ⟨g.1.comp f.1, g.2.comp f.2⟩

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) :
    f = g := by
  apply Subtype.ext
  apply Partite.Embedding.ext
  exact h

instance [Finite V] [Finite W] : Finite (Embedding A B) :=
  Finite.of_injective Subtype.val Subtype.val_injective


def toRelClosed (e : Embedding A B) :
    RelStructure.ClosedEmbedding A.toRelStructure B.toRelStructure :=
  ⟨e.1.toEmbedding, e.2⟩

end Embedding

def Arrow (A : Partite.System L.graph P V)
    (B : Partite.System L.graph P W)
    {X : Type v} (C : Partite.System L.graph P X)
    (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C,
    ∀ e₁ e₂ : Embedding A B,
      χ (Embedding.comp f e₁) = χ (Embedding.comp f e₂)

namespace Induced

variable (A : RelStructure L.graph P)
    (B : Partite.System L.graph P V)

abbrev Letter := Embedding (Partite.transversal A) B

instance [Finite P] [Finite V] : Finite (Letter A B) :=
  Finite.of_injective Subtype.val Subtype.val_injective

variable {A B} {N : ℕ}

/-- Forget closedness from a line alphabet. -/
def forgetLine (W : Line (Letter A B) N) :
    Line (Partite.Induced.Letter A B) N where
  symbol i := match W.symbol i with
    | .parameter => .parameter
    | .const e => .const e.1
  hasParameter := by
    obtain ⟨i, hi⟩ := W.hasParameter
    refine ⟨i, ?_⟩
    change (match W.symbol i with
      | .parameter => LineSymbol.parameter
      | .const e => LineSymbol.const e.1) = .parameter
    rw [hi]

def lineMap (W : Line (Letter A B) N) (x : V) :
    Partite.Induced.Vertex B N :=
  Partite.NonInduced.lineMap (forgetLine W) x

theorem lineMap_injective (W : Line (Letter A B) N) :
    Function.Injective (lineMap W) :=
  Partite.NonInduced.lineMap_injective (forgetLine W)

/-- U-transversality is preserved by coordinate powers. -/
theorem power_uTransversal
    (hU : B.FunctionOutputTransversal) :
    (Partite.Induced.power B N).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  apply Partite.NonInduced.Vertex.ext B hp
  intro k
  let args : Fin (L.funcArity F) → V :=
    fun i => (x i).coord k
  have hyk : B.rel (.inr F)
      (Structure.funcTuple args (y.coord k)) := by
    have h := hy k
    have ht :
        Structure.funcTuple args (y.coord k) =
          (fun j => (Structure.funcTuple x y j).coord k) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [args, Structure.funcTuple]
      · simp [args, Structure.funcTuple]
    rw [ht]
    exact h
  have hzk : B.rel (.inr F)
      (Structure.funcTuple args (z.coord k)) := by
    have h := hz k
    have ht :
        Structure.funcTuple args (z.coord k) =
          (fun j => (Structure.funcTuple x z j).coord k) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [args, Structure.funcTuple]
      · simp [args, Structure.funcTuple]
    rw [ht]
    exact h
  apply hU F args (y.coord k) (z.coord k) hyk hzk
  exact (y.belongs k).trans (hp.trans (z.belongs k).symm)

def linePartiteEmbedding
    (hB : B.IsPartiteOver A)
    (W : Line (Letter A B) N) :
    Partite.Embedding B (Partite.Induced.power B N) :=
  Partite.Induced.lineEmbedding hB (forgetLine W)

/-- A Hales--Jewett line map is U-closed. -/
theorem lineMap_closed
    (hB : B.IsPartiteOver A)
    (hU : B.FunctionOutputTransversal)
    (W : Line (Letter A B) N) :
    RelStructure.FunctionClosedMap
      B.toRelStructure
      (Partite.Induced.power B N).toRelStructure
      (lineMap W) := by
  classical
  intro F x z hz
  obtain ⟨i0, hi0⟩ := W.hasParameter
  let y : V := z.coord i0
  have hy : B.rel (.inr F) (Structure.funcTuple x y) := by
    have hcoord := hz i0
    have ht :
        Structure.funcTuple x y =
          (fun j =>
            (Structure.funcTuple (lineMap W ∘ x) z j).coord i0) := by
      funext j
      refine Fin.lastCases ?_ (fun q => ?_) j
      · simp [lineMap, y, Structure.funcTuple,
          Partite.NonInduced.lineMap, forgetLine, hi0]
      · simp [lineMap, Structure.funcTuple,
          Partite.NonInduced.lineMap, forgetLine, hi0,
          Function.comp_apply]
    rw [ht]
    exact hcoord
  refine ⟨y, hy, ?_⟩
  apply Partite.NonInduced.Vertex.ext B
  · simpa [lineMap, y, Partite.NonInduced.lineMap] using z.belongs i0
  · intro i
    cases hi : W.symbol i with
    | parameter =>
        have hzi : B.rel (.inr F)
            (Structure.funcTuple x (z.coord i)) := by
          have hcoord := hz i
          have ht :
              Structure.funcTuple x (z.coord i) =
                (fun j =>
                  (Structure.funcTuple (lineMap W ∘ x) z j).coord i) := by
            funext j
            refine Fin.lastCases ?_ (fun q => ?_) j
            · simp [lineMap, Structure.funcTuple,
                Partite.NonInduced.lineMap, forgetLine, hi]
            · simp [lineMap, Structure.funcTuple,
                Partite.NonInduced.lineMap, forgetLine, hi,
                Function.comp_apply]
          rw [ht]
          exact hcoord
        have hparts : B.part y = B.part (z.coord i) :=
          (z.belongs i0).trans (z.belongs i).symm
        have heq := hU F x y (z.coord i) hy hzi hparts
        simpa [lineMap, Partite.NonInduced.lineMap,
          forgetLine, hi] using heq
    | const e =>
        have hPartTuple :
            B.part ∘ Structure.funcTuple x y =
              Structure.funcTuple (B.part ∘ x) (B.part y) := by
          funext j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simp [Structure.funcTuple]
          · simp [Structure.funcTuple, Function.comp_apply]
        have hA0 :=
          hB.1 (.inr F) (Structure.funcTuple x y) hy
        have hA :
            A.rel (.inr F)
              (Structure.funcTuple (B.part ∘ x) (B.part y)) := by
          rw [← hPartTuple]
          exact hA0
        have heRel0 :=
          (e.1.toEmbedding.map_rel_iff
            (.inr F)
            (Structure.funcTuple (B.part ∘ x) (B.part y))).mpr hA
        let eargs : Fin (L.funcArity F) → V :=
          fun q => e (B.part (x q))
        have heTuple :
            e.1 ∘ Structure.funcTuple (B.part ∘ x) (B.part y) =
              Structure.funcTuple eargs (e (B.part y)) := by
          funext j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simp [eargs, Structure.funcTuple, Function.comp_apply]
          · simp [eargs, Structure.funcTuple, Function.comp_apply]
        have heValue :
            B.rel (.inr F)
              (Structure.funcTuple eargs (e (B.part y))) := by
          rw [← heTuple]
          exact heRel0
        have hzi :
            B.rel (.inr F)
              (Structure.funcTuple eargs (z.coord i)) := by
          have hcoord := hz i
          have ht :
              Structure.funcTuple eargs (z.coord i) =
                (fun j =>
                  (Structure.funcTuple (lineMap W ∘ x) z j).coord i) := by
            funext j
            refine Fin.lastCases ?_ (fun q => ?_) j
            · simp [lineMap, eargs, Structure.funcTuple,
                Partite.NonInduced.lineMap, forgetLine, hi]
            · simp [lineMap, eargs, Structure.funcTuple,
                Partite.NonInduced.lineMap, forgetLine, hi,
                Function.comp_apply]
          rw [ht]
          exact hcoord
        have hparts :
            B.part (e (B.part y)) = B.part (z.coord i) := by
          calc
            B.part (e (B.part y)) = B.part y :=
              e.1.map_part (B.part y)
            _ = z.part := z.belongs i0
            _ = B.part (z.coord i) := (z.belongs i).symm
        have heq :=
          hU F eargs (e (B.part y)) (z.coord i)
            heValue hzi hparts
        simpa [lineMap, Partite.NonInduced.lineMap,
          forgetLine, hi] using heq

def lineEmbedding
    (hB : B.IsPartiteOver A)
    (hU : B.FunctionOutputTransversal)
    (W : Line (Letter A B) N) :
    Embedding B (Partite.Induced.power B N) :=
  ⟨linePartiteEmbedding hB W, lineMap_closed hB hU W⟩

def firstLine (hN : 0 < N) (w : Fin N → Letter A B) :
    Line (Letter A B) N where
  symbol i := if i = ⟨0, hN⟩ then .parameter else .const (w i)
  hasParameter := ⟨⟨0, hN⟩, by simp⟩

@[simp] theorem firstLine_eval (hN : 0 < N)
    (w : Fin N → Letter A B) :
    (firstLine hN w).eval (w ⟨0, hN⟩) = w := by
  funext i
  by_cases hi : i = ⟨0, hN⟩
  · subst i
    simp [firstLine, Line.eval, LineSymbol.eval]
  · simp [firstLine, Line.eval, LineSymbol.eval, hi]

def wordEmbedding
    (hB : B.IsPartiteOver A)
    (hU : B.FunctionOutputTransversal)
    (hN : 0 < N)
    (w : Fin N → Letter A B) :
    Embedding (Partite.transversal A) (Partite.Induced.power B N) :=
  Embedding.comp (lineEmbedding hB hU (firstLine hN w)) (w ⟨0, hN⟩)

theorem lineEmbedding_comp_letter
    (hB : B.IsPartiteOver A)
    (hU : B.FunctionOutputTransversal)
    (hN : 0 < N)
    (W : Line (Letter A B) N)
    (e : Letter A B) :
    Embedding.comp (lineEmbedding hB hU W) e =
      wordEmbedding hB hU hN (W.eval e) := by
  apply Embedding.ext
  intro p
  change
    Partite.NonInduced.lineMap (forgetLine W) (e p) =
      Partite.NonInduced.lineMap
        (forgetLine (firstLine hN (W.eval e)))
        ((W.eval e ⟨0, hN⟩) p)
  have hleft :=
    Partite.NonInduced.lineMap_comp_letter
      (forgetLine W) e.1 p
  rw [hleft]
  have hEval :
      (forgetLine W).eval e.1 =
        fun i => ((W.eval e) i).1 := by
    funext i
    cases hi : W.symbol i with
    | parameter =>
        simp [forgetLine, Line.eval, LineSymbol.eval, hi]
    | const d =>
        simp [forgetLine, Line.eval, LineSymbol.eval, hi]
  rw [hEval]
  have hright :=
    Partite.NonInduced.lineMap_comp_letter
      (forgetLine (firstLine hN (W.eval e)))
      ((W.eval e ⟨0, hN⟩).1) p
  rw [hright]
  have hEvalFirst :
      (forgetLine (firstLine hN (W.eval e))).eval
          ((W.eval e ⟨0, hN⟩).1) =
        fun i => ((W.eval e) i).1 := by
    funext i
    by_cases hi : i = ⟨0, hN⟩
    · subst i
      simp [forgetLine, firstLine, Line.eval, LineSymbol.eval]
    · simp [forgetLine, firstLine, Line.eval, LineSymbol.eval, hi]
  rw [hEvalFirst]

/-- Induced Partite Lemma with closures. -/
theorem partiteLemma
    (hB : B.IsPartiteOver A)
    (hU : B.FunctionOutputTransversal)
    [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧
      (Partite.Induced.power B N).FunctionOutputTransversal ∧
      Arrow (Partite.transversal A) B
        (Partite.Induced.power B N) κ := by
  classical
  letI : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, power_uTransversal hU, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ :=
    hHJ (fun w => χ (wordEmbedding hB hU hN w))
  refine ⟨lineEmbedding hB hU W, ?_⟩
  intro e₁ e₂
  simpa only [lineEmbedding_comp_letter hB hU hN]
    using hW e₁ e₂

end Induced
end StructuralRamsey.Partite.Closed
