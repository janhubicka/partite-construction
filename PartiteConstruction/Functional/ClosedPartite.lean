import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Induced
import PartiteConstruction.HalesJewett.Finite

/-! # Induced Partite Lemma with U-closed embeddings

This is the relational-graph version used for genuine set-valued functions.
The alphabet consists of U-closed partite embeddings, the coordinate power
preserves U-transversality, and every Hales--Jewett word/line map is U-closed.
-/
namespace StructuralRamsey.Partite.Closed

open RelStructure HalesJewett SuccessorTree Structure

universe u v
variable {L : Language.{u}} {P V W : Type v}

structure Embedding (A : Partite.System L.graph P V)
    (B : Partite.System L.graph P W)
    extends Partite.Embedding A B where
  closed : RelStructure.FunctionClosedMap
    A.toRelStructure B.toRelStructure toFun

instance {A : Partite.System L.graph P V}
    {B : Partite.System L.graph P W} :
    CoeFun (Embedding A B) (fun _ => V → W) :=
  ⟨fun e => e.toEmbedding⟩

namespace Embedding

variable {A : Partite.System L.graph P V}
  {B : Partite.System L.graph P W}

@[ext] theorem ext {f g : Embedding A B} (h : ∀ x, f x = g x) :
    f = g := by
  cases f; cases g
  simp only [mk.injEq]
  exact Partite.Embedding.ext h

def id (A : Partite.System L.graph P V) : Embedding A A where
  toEmbedding := Partite.Embedding.id A
  closed := by
    intro F x y hy
    exact ⟨y, hy, rfl⟩

def comp {X : Type*} {C : Partite.System L.graph P X}
    (g : Embedding B C) (f : Embedding A B) :
    Embedding A C where
  toEmbedding := g.toEmbedding.comp f.toEmbedding
  closed := g.closed.comp f.closed

def toRelClosed (e : Embedding A B) :
    RelStructure.ClosedEmbedding A.toRelStructure B.toRelStructure where
  toEmbedding := e.toEmbedding.toEmbedding
  closed := e.closed

end Embedding

def Arrow (A : Partite.System L.graph P V)
    (B : Partite.System L.graph P W)
    {X : Type*} (C : Partite.System L.graph P X)
    (κ : Type*) : Prop :=
  ∀ χ : Embedding A C → κ, ∃ f : Embedding B C,
    ∀ e₁ e₂ : Embedding A B,
      χ (f.comp e₁) = χ (f.comp e₂)

namespace Induced

variable (A : RelStructure L.graph P)
    (B : Partite.System L.graph P V)

abbrev Letter :=
  Embedding (Partite.transversal A) B

variable {A B} {N : ℕ}

/-- Forget closedness from a line alphabet. -/
def forgetLine (W : Line (Letter A B) N) :
    Line (Partite.Induced.Letter A B) N where
  symbol i := match W.symbol i with
    | .parameter => .parameter
    | .const e => .const e.toEmbedding
  hasParameter := by
    obtain ⟨i, hi⟩ := W.hasParameter
    exact ⟨i, by simp [hi]⟩

@[simp] theorem forgetLine_symbol_parameter
    (W : Line (Letter A B) N) {i : Fin N}
    (hi : W.symbol i = .parameter) :
    (forgetLine W).symbol i = .parameter := by
  simp [forgetLine, hi]

@[simp] theorem forgetLine_symbol_const
    (W : Line (Letter A B) N) {i : Fin N}
    {e : Letter A B} (hi : W.symbol i = .const e) :
    (forgetLine W).symbol i = .const e.toEmbedding := by
  simp [forgetLine, hi]

def lineMap (W : Line (Letter A B) N) (x : V) :
    Partite.Induced.Vertex B N :=
  Partite.NonInduced.lineMap (forgetLine W) x

theorem lineMap_injective (W : Line (Letter A B) N) :
    Function.Injective (lineMap W) :=
  Partite.NonInduced.lineMap_injective (forgetLine W)

/-- U-transversality is preserved by coordinate powers. -/
theorem power_uTransversal
    (hU : B.UTransversal) :
    (Partite.Induced.power B N).UTransversal := by
  intro F x y z hy hz hp
  apply Partite.NonInduced.Vertex.ext B hp
  intro k
  let args : Fin (L.funcArity F) → V :=
    fun i => (x i).coord k
  have hyk : B.rel (.inr F)
      (Structure.funcTuple args (y.coord k)) := by
    have h := hy k
    convert h using 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [args, Structure.funcTuple]
    · simp [args, Structure.funcTuple]
  have hzk : B.rel (.inr F)
      (Structure.funcTuple args (z.coord k)) := by
    have h := hz k
    convert h using 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [args, Structure.funcTuple]
    · simp [args, Structure.funcTuple]
  apply hU F args (y.coord k) (z.coord k) hyk hzk
  exact (y.belongs k).trans (hp.trans (z.belongs k).symm)

/-- Every closed line gives the same ordinary induced embedding as in the
relational Partite Lemma. -/
def linePartiteEmbedding
    (hB : B.IsPartiteOver A)
    (W : Line (Letter A B) N) :
    Partite.Embedding B (Partite.Induced.power B N) :=
  Partite.Induced.lineEmbedding hB (forgetLine W)

/-- A Hales--Jewett line map is U-closed.  A parameter coordinate recovers the
source output; U-transversality forces all other coordinates to come from that
same output. -/
theorem lineMap_closed
    (hB : B.IsPartiteOver A)
    (hU : B.UTransversal)
    (W : Line (Letter A B) N) :
    RelStructure.FunctionClosedMap
      B.toRelStructure
      (Partite.Induced.power B N).toRelStructure
      (lineMap W) := by
  classical
  intro F x z hz
  obtain ⟨i0, hi0⟩ := W.hasParameter
  let y : V := z.coord i0
  let args0 : Fin (L.funcArity F) → V := x
  have hy : B.rel (.inr F) (Structure.funcTuple x y) := by
    have hi := hz
    change
      (Partite.Induced.power B N).rel (.inr F)
        (Structure.funcTuple (lineMap W ∘ x) z) at hi
    have hcoord := hi i0
    convert hcoord using 1
    funext j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · simp [lineMap, y, Structure.funcTuple,
        Partite.NonInduced.lineMap, forgetLine, hi0]
    · simp [lineMap, Structure.funcTuple,
        Partite.NonInduced.lineMap, forgetLine, hi0,
        Function.comp_apply]
  refine ⟨y, hy, ?_⟩
  apply Partite.NonInduced.Vertex.ext B
  · simpa [lineMap, y, Partite.NonInduced.lineMap] using z.belongs i0
  · intro i
    cases hi : W.symbol i with
    | parameter =>
        have hzi : B.rel (.inr F)
            (Structure.funcTuple x (z.coord i)) := by
          have hcoord := hz i
          convert hcoord using 1
          funext j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simp [lineMap, Structure.funcTuple,
              Partite.NonInduced.lineMap, forgetLine, hi,
              Function.comp_apply]
          · simp [lineMap, Structure.funcTuple,
              Partite.NonInduced.lineMap, forgetLine, hi,
              Function.comp_apply]
        have hparts : B.part y = B.part (z.coord i) :=
          (z.belongs i0).trans (z.belongs i).symm
        have heq := hU F x y (z.coord i) hy hzi hparts
        simpa [lineMap, Partite.NonInduced.lineMap,
          forgetLine, hi] using heq
    | const e =>
        have hA :
            A.rel (.inr F)
              (Structure.funcTuple (B.part ∘ x) (B.part y)) := by
          exact hB.1 (.inr F) (Structure.funcTuple x y) hy
        have heRel :
            B.rel (.inr F)
              (e.toEmbedding.toEmbedding ∘
                Structure.funcTuple (B.part ∘ x) (B.part y)) :=
          (e.toEmbedding.toEmbedding.map_rel_iff
            (.inr F)
            (Structure.funcTuple (B.part ∘ x) (B.part y))).mpr hA
        let eargs : Fin (L.funcArity F) → V :=
          fun q => e (B.part (x q))
        have heValue :
            B.rel (.inr F)
              (Structure.funcTuple eargs (e (B.part y))) := by
          convert heRel using 1
          funext j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simp [eargs, Structure.funcTuple]
          · simp [eargs, Structure.funcTuple, Function.comp_apply]
        have hzi :
            B.rel (.inr F)
              (Structure.funcTuple eargs (z.coord i)) := by
          have hcoord := hz i
          convert hcoord using 1
          funext j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simp [lineMap, eargs, Structure.funcTuple,
              Partite.NonInduced.lineMap, forgetLine, hi,
              Function.comp_apply]
          · simp [lineMap, eargs, Structure.funcTuple,
              Partite.NonInduced.lineMap, forgetLine, hi,
              Function.comp_apply]
        have hparts :
            B.part (e (B.part y)) = B.part (z.coord i) := by
          calc
            B.part (e (B.part y)) = B.part y :=
              e.toEmbedding.map_part (B.part y)
            _ = z.part := z.belongs i0
            _ = B.part (z.coord i) := (z.belongs i).symm
        have heq :=
          hU F eargs (e (B.part y)) (z.coord i)
            heValue hzi hparts
        simpa [lineMap, Partite.NonInduced.lineMap,
          forgetLine, hi] using heq

def lineEmbedding
    (hB : B.IsPartiteOver A)
    (hU : B.UTransversal)
    (W : Line (Letter A B) N) :
    Embedding B (Partite.Induced.power B N) where
  toEmbedding := linePartiteEmbedding hB W
  closed := lineMap_closed hB hU W

def firstLine (hN : 0 < N) (w : Fin N → Letter A B) :
    Line (Letter A B) N where
  symbol i := if i = ⟨0, hN⟩ then .parameter else .const (w i)
  hasParameter := ⟨⟨0, hN⟩, by simp⟩

def wordEmbedding
    (hB : B.IsPartiteOver A)
    (hU : B.UTransversal)
    (hN : 0 < N)
    (w : Fin N → Letter A B) :
    Embedding (Partite.transversal A) (Partite.Induced.power B N) :=
  (lineEmbedding hB hU (firstLine hN w)).comp (w ⟨0, hN⟩)

@[simp] theorem firstLine_eval (hN : 0 < N)
    (w : Fin N → Letter A B) :
    (firstLine hN w).eval (w ⟨0, hN⟩) = w := by
  funext i
  by_cases hi : i = ⟨0, hN⟩
  · subst i
    simp [firstLine, Line.eval, LineSymbol.eval]
  · simp [firstLine, Line.eval, LineSymbol.eval, hi]

theorem lineEmbedding_comp_letter
    (hB : B.IsPartiteOver A)
    (hU : B.UTransversal)
    (hN : 0 < N)
    (W : Line (Letter A B) N)
    (e : Letter A B) :
    (lineEmbedding hB hU W).comp e =
      wordEmbedding hB hU hN (W.eval e) := by
  apply Embedding.ext
  intro p
  change
    Partite.NonInduced.lineMap (forgetLine W) (e p) =
      Partite.NonInduced.lineMap
        (forgetLine (firstLine hN (W.eval e)))
        ((W.eval e ⟨0, hN⟩) p)
  rw [← Partite.NonInduced.lineMap_comp_letter
    (forgetLine W) e.toEmbedding p]
  have hEval :
      (forgetLine W).eval e.toEmbedding =
        fun i => ((W.eval e) i).toEmbedding := by
    funext i
    cases hi : W.symbol i with
    | parameter =>
        simp [forgetLine, Line.eval, LineSymbol.eval, hi]
    | const d =>
        simp [forgetLine, Line.eval, LineSymbol.eval, hi]
  rw [hEval]
  have hfirst := Partite.NonInduced.wordEmbedding_apply
    (A := A) (B := B) hN
    (fun i => ((W.eval e) i).toEmbedding) p
  exact hfirst.symm

/-- Induced Partite Lemma with closures, for the function-graph relations. -/
theorem partiteLemma
    (hB : B.IsPartiteOver A)
    (hU : B.UTransversal)
    [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧
      (Partite.Induced.power B N).UTransversal ∧
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
