import PartiteConstruction.Functional.ClosedOccupiedARelativeMark
import PartiteConstruction.Functional.WeakHistoryShadowCardinality
import PartiteConstruction.Functional.ProjectedHistoryFactor

/-!
# Ordinary predecessor rank gives a protected A-mark over any CLOSED occupied boundary

The verified ordinary rank-m exact weak-test history invariant of D
already supplies a strict full-functional Base-tree completion with
actual ambient A-copy intersection certificates. When the occupied
alpha-boundary H={a | alpha(a)∈I} is FUNCTION-CLOSED in A, a fresh
Base-copy can be attached along the genuine FULL functional A.induce H
root, yielding an exact protected alpha-mark on the SAME weak I.

This is not the false unconditional protected-mark predecessor; its
extra hypothesis is the semantic U-closedness of this PARTICULAR
occupied partial A-boundary, precisely as in the relational
relative-labelled proof. All singleton projected histories are only
TARGET certificate bookkeeping: no source vertex or closure hull
is added to I, and the caller's original histories remain protected.

This lemma is the ingredient for a genuine strict functional
maximal-image mixed step when both projected occupied A-boundaries
are closed. General nonclosed H remains open.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost

universe u v
variable {L : Language.{u}} {UA VB P : Type v}

/-- From the ORDINARY strict B-tree predecessor rank-m property on D,
complete any weak I of ≤m vertices with a safe full selected alpha
mark, provided its occupied alpha-boundary is FULL/FUNCTION-CLOSED.

The extra alpha vertices live only in a fresh TARGET Base-copy and
do not count against the predecessor's exact weak vertex budget. -/
theorem protected_of_closedOccupiedA
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} [Fintype P]
    {m : ℕ}
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (eAB : Embedding A Base)
    (hBase : Base.Irreducible)
    (alpha : Embedding A D)
    (I : Finset P) (hI : I.card ≤ m)
    (hClosed : A.IsClosed
      {a : UA | alpha a ∈ (↑I : Set P)})
    (history : List (Set P)) :
    SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P)
      (↑I : Set P) history := by
  classical
  let extended := history ++ singletonProjectedHistory P
  have hSingletons : ∀ q : P, Set.singleton q ∈ extended := by
    intro q
    exact List.mem_append.mpr
      (Or.inr (singleton_mem_singletonProjectedHistory q))
  have hPrevious :
      SetAmbientRelativeWeakTreeWitness
        A Base D (id : P → P)
        (↑I : Set P) extended :=
    hPrev I hI extended
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies,
      hHist, mark, hContained, hTrace⟩ :=
    hPrevious.protected_of_closedOccupiedA
      eAB hBase alpha (↑I : Set P)
      hClosed extended hSingletons
  have hHistory :
      SetRespectsProjectedHistory (id : P → P)
        (↑I : Set P) f history := by
    intro K hK x y hEq
    exact hHist K (List.mem_append.mpr (Or.inl hK)) x y hEq
  exact ⟨Z, Target, hTree, f, hWeak, hCopies,
    hHistory, mark, hContained, hTrace⟩

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost
