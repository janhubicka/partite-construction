import PartiteConstruction.Structure.GenericUGraphPower
import PartiteConstruction.Partite.NonInduced

/-!
# Track F: actual Hales–Jewett word and line maps under U-graph reindex

The first induced partite lemma uses genuine letters (part-preserving
induced embeddings), words in those letters, and parameter lines. Their
underlying maps do not depend on a renaming of relation symbols.

This checks exact naturality of those concrete maps for the nonredundant
arbitrary-(L,U) relation/function graph reindex, using the *actual*
tagged vertex equivalence of merged Track F #590. No Ramsey theorem or
Picture step is assumed here.
-/

namespace StructuralRamsey.Partite.GenericUGraphHJ

open HalesJewett

universe u v w

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- Reindex an actual Hales–Jewett letter, preserving its vertex map. -/
noncomputable def letterReindex
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Partite.NonInduced.Letter A B) :
    Partite.NonInduced.Letter
      (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU) :=
  e.asReducedUGraph U hU

@[simp] theorem letterReindex_apply
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Partite.NonInduced.Letter A B)
    (p : P) :
    letterReindex A B U hU e p = e p := rfl

/-- Actual HJ word vertices commute with the same-carrier tagged-power
equivalence, preserving every named part and coordinate. -/
theorem wordMap_reindex
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ)
    (w : Fin N → Partite.NonInduced.Letter A B)
    (p : P) :
    Partite.NonInduced.Vertex.uGraphEquiv B U hU N
      (Partite.NonInduced.wordMap w p) =
    Partite.NonInduced.wordMap
      (fun i => letterReindex A B U hU (w i)) p := by
  apply Partite.NonInduced.Vertex.ext (B.asReducedUGraph U hU)
  · rfl
  · intro i
    rfl

/-- Reindex an actual parameter line without changing parameter or
constant positions, so its Hales–Jewett combinatorics is unchanged. -/
noncomputable def lineReindex
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {N : ℕ}
    (W : Line (Partite.NonInduced.Letter A B) N) :
    Line (Partite.NonInduced.Letter
      (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU)) N where
  symbol i := match W.symbol i with
    | .parameter => .parameter
    | .const e => .const (letterReindex A B U hU e)
  hasParameter := by
    obtain ⟨i, hi⟩ := W.hasParameter
    refine ⟨i, ?_⟩
    simp [hi]

/-- The actual line injection f_W commutes with HJ reindex, again on
literally the same vertex map into the tagged power. -/
theorem lineMap_reindex
    (A : RelStructure L P) (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {N : ℕ}
    (W : Line (Partite.NonInduced.Letter A B) N)
    (x : V) :
    Partite.NonInduced.Vertex.uGraphEquiv B U hU N
      (Partite.NonInduced.lineMap W x) =
    Partite.NonInduced.lineMap
      (lineReindex A B U hU W) x := by
  apply Partite.NonInduced.Vertex.ext (B.asReducedUGraph U hU)
  · rfl
  · intro i
    cases hi : W.symbol i with
    | parameter =>
        simp [Partite.NonInduced.lineMap, lineReindex, hi]
    | const e =>
        simp [Partite.NonInduced.lineMap, lineReindex, hi]

end StructuralRamsey.Partite.GenericUGraphHJ
