import PartiteConstruction.Functional.ProjectedHistoryFactor
import PartiteConstruction.Functional.TreeExtensionHistoryInduction

/-! # Automatic projection synchronization in relative functional gluing

For finite outer carriers, adjoin the singleton projected-history diary to
the requested finite history.  A relative completion on one side then
determines a factor map from the distinguished target root tree to the
outer carrier.  Exact source free-amalgam overlap ensures that this factor
map also works on the second side.

Consequently two relative strict-tree witnesses over the same root glue
without an extra ambient projection-compatibility assumption.  Crucially,
the conclusion remains a *relative* extension of the original root tree,
so the operation can be used recursively for several attached copies.
The singleton diary is internal bookkeeping, not an additional conclusion.
-/

namespace StructuralRamsey.Structure.HasTreeExtensionProjectedHistoryCompletion

universe u v

variable {L : Language.{u}}
variable {VB H E P G : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H} {Side : Structure L E}
variable {Start : Structure L G}

/-- The history of all singleton sets forces the outer projection on the
embedded source root to factor through the target root map.  This follows
from the relative witness itself: equality in the root tree implies
equality of the two associated side points. -/
theorem projectionFactorsThroughRoot
    [Nonempty P]
    {s : Embedding Root Side} {q : H → G} {p : E → P}
    {history : List (Set P)}
    (h : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p history)
    (hSingle : ∀ a : P, Set.singleton a ∈ history) :
    ∃ pG : G → P, ∀ d, p (s d) = pG (q d) := by
  obtain ⟨Z, T, hExt, f, _hf, hcompat, _hIso, hHist⟩ := h
  have hRootHist :
      ∀ K ∈ history, ∀ x y : H,
        q x = q y → (p (s x) ∈ K ↔ p (s y) ∈ K) := by
    intro K hK x y hxy
    apply hHist K hK (s x) (s y)
    calc
      f (s x) = hExt.startEmbedding (q x) := hcompat x
      _ = hExt.startEmbedding (q y) :=
        congrArg hExt.startEmbedding hxy
      _ = f (s y) := (hcompat y).symm
  exact projectedMap_factors_of_singletonHistory
    (fun d => p (s d)) q history hSingle hRootHist

end StructuralRamsey.Structure.HasTreeExtensionProjectedHistoryCompletion


namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {VB H E F C P G : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C} {Start : Structure L G}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Two relative completions of the sides of a source free amalgam, over
one common strict tree root, glue to another relative completion.

The proof constructs the finite singleton diary automatically.  The
remaining history requirements are those requested by the caller; no
assumption that the root projection is injective or separately factors
through its target completion is needed. -/
theorem glueRelative_withAutomaticProjectedHistory
    [Fintype P] [Nonempty P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (q : H → G)
    (pWhole : C → P)
    (history : List (Set P))
    (hLeft :
      HasTreeExtensionProjectedHistoryCompletion
        (Base := Base) (Start := Start) sL q (pWhole ∘ iL)
        (history ++ singletonProjectedHistory P))
    (hRight :
      HasTreeExtensionProjectedHistoryCompletion
        (Base := Base) (Start := Start) sR q (pWhole ∘ iR)
        (history ++ singletonProjectedHistory P)) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start)
      (iL.comp sL) q pWhole history := by
  let allHistory : List (Set P) :=
    history ++ singletonProjectedHistory P
  have hSingle : ∀ a : P, Set.singleton a ∈ allHistory := by
    intro a
    apply List.mem_append.mpr
    exact Or.inr (singleton_mem_singletonProjectedHistory a)
  obtain ⟨pG, hRootL⟩ :=
    HasTreeExtensionProjectedHistoryCompletion.projectionFactorsThroughRoot
      (Base := Base) hLeft hSingle
  have hRootR :
      ∀ d, (pWhole ∘ iR) (sR d) = pG (q d) := by
    intro d
    have hOverlap : iL (sL d) = iR (sR d) :=
      (hSrc.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
    calc
      (pWhole ∘ iR) (sR d) = pWhole (iR (sR d)) := rfl
      _ = pWhole (iL (sL d)) :=
        congrArg pWhole hOverlap.symm
      _ = pG (q d) := hRootL d
  have hCombined :
      HasTreeExtensionProjectedHistoryCompletion
        (Base := Base) (Start := Start)
        (iL.comp sL) q pWhole allHistory :=
    HasTreeExtensionProjectedHistoryCompletion.glue_relative
      hSrc q pWhole (pWhole ∘ iL) (pWhole ∘ iR) pG
      (fun _ => rfl) (fun _ => rfl)
      hRootL hRootR allHistory hLeft hRight
  exact hCombined.mono_history (fun K hK =>
    List.mem_append.mpr (Or.inl hK))

end StructuralRamsey.Structure.LocallyClosedTreeCompletable
