import PartiteConstruction.Functional.ClosedOccupiedARelativeMark
import PartiteConstruction.Functional.ClosedOccupiedAPredecessor

/-!
# Closed-control-only predecessor witnesses for the strict functional iteration

The original exact-weak AtMost predecessor requires strict
full-functional Base-tree history witnesses for EVERY finite weak
test of the control. Here we isolate a genuinely weaker
AtMostClosed invariant: tests I must be function-closed in D,
but retain arbitrary finite projected histories and actual full
ambient A-copy intersection certificates.

On a function-closed I whose occupied selected alpha(A) root
is also function-closed, the already verified fresh TARGET
Base-copy construction supplies a safe protected FULL A-mark,
without adding source vertices or increasing the rank budget.

This is the correct predecessor interface for seeking a
closed-source unary functional n-pass proof. It is NOT a
universal marked-root lemma for arbitrary weak I, and does
not itself prove the next HJ Picture iteration.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB P : Type v}

/-- Strict full-functional rank-m history witnesses restricted
ONLY to genuinely function-closed finite subsets of a functional
control D. This includes every requested history and actual full
ambient A-copy intersections, not a weaker target property. -/
def AtMostClosed
    (A : Structure L UA) (Base : Structure L VB)
    (D : Structure L P) (m : ℕ) : Prop :=
  ∀ (I : Finset P), I.card ≤ m →
    D.IsClosed (↑I : Set P) →
    ∀ history : List (Set P),
      SetAmbientRelativeWeakTreeWitness
        A Base D (id : P → P) (↑I : Set P) history

/-- The old exact-weak rank-m predecessor implies the
closed-test predecessor. The converse is NOT asserted. -/
theorem AtMost.toClosed
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} {m : ℕ}
    (hPrev : AtMost A Base D (id : P → P) m) :
    AtMostClosed A Base D m := by
  intro I hI _hClosed history
  exact hPrev I hI history

namespace AtMostClosed

/-- A CLOSED exact projected test I within rank m obtains a
strict full-functional protected alpha-mark by attaching ONE
fresh TARGET Base-copy along the FULL occupied A.induce H root.

The caller's arbitrary projected histories remain preserved;
singleton histories are temporarily requested only to exclude
wrong target hits at occupied labels. No source/test vertices
are added, and every set-valued function fibre is genuine. -/
theorem protected_of_closedOccupiedA
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} [Fintype P]
    {m : ℕ}
    (hPrev : AtMostClosed A Base D m)
    (eAB : Embedding A Base)
    (hBase : Base.Irreducible)
    (alpha : Embedding A D)
    (I : Finset P) (hI : I.card ≤ m)
    (hIClosed : D.IsClosed (↑I : Set P))
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
  have hAlphaClosed : A.IsClosed
      {a : UA | alpha a ∈ (↑I : Set P)} :=
    alpha.preimage_isClosed (↑I : Set P) hIClosed
  have hPrevious :
      SetAmbientRelativeWeakTreeWitness
        A Base D (id : P → P)
        (↑I : Set P) extended :=
    hPrev I hI hIClosed extended
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies,
      hHist, mark, hContained, hTrace⟩ :=
    hPrevious.protected_of_closedOccupiedA
      eAB hBase alpha (↑I : Set P)
      hAlphaClosed extended hSingletons
  have hHistory :
      SetRespectsProjectedHistory (id : P → P)
        (↑I : Set P) f history := by
    intro K hK x y hEq
    exact hHist K (List.mem_append.mpr (Or.inl hK)) x y hEq
  exact ⟨Z, Target, hTree, f, hWeak, hCopies,
    hHistory, mark, hContained, hTrace⟩

end AtMostClosed
end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
