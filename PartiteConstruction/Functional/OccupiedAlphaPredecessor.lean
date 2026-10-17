import PartiteConstruction.Functional.OccupiedAlphaMark
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Extraction of the occupied marked boundary from the verified predecessor

Let D be the previous genuine functional control, and suppose its
EXACT n-vertex weak-test invariant supplies strict full-functional
Base-tree witnesses with actual ambient-A-copy intersections and
arbitrary projected histories.

For any I⊆D of size ≤n and any full alpha:A↪D, call that invariant
with the user's history PLUS all projected singleton sets. The
returned ordinary witness automatically has a full A mark whose
coordinates are exact on precisely the OCCUPIED alpha(A) labels.

If alpha(A) is contained in I, all positions are occupied, hence
we get an exact protected full A-mark from the ORDINARY predecessor
invariant. The important missing-boundary case is expressly not
claimed, and the false universal marked-A induction is not used.

Source weak vertices, image size and function fibres are unchanged.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost

universe u v
variable {L : Language.{u}} {UA VB P : Type v}

/-- Every exact weak predecessor witness has a *partially protected*
full A mark on the labels currently occupied by I, together with
the original history requested by the caller.

The source remains the literal weak D|I; the temporary singleton
history is only target certificate data, not an enlargement of I. -/
theorem occupiedAlpha_witness
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} [Fintype P] [DecidableEq P]
    {m : ℕ}
    (hPrev : AtMost A Base D (id : P → P) m)
    (I : Finset P) (hI : I.card ≤ m)
    (alpha : Embedding A D)
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : (↑I : Set P) → Z,
        IsAmbientRelativeWeakHE D (↑I : Set P) Target f ∧
        SetAmbientACopyIntersections A D Target (↑I : Set P) f ∧
        SetRespectsProjectedHistory (id : P → P)
          (↑I : Set P) f history ∧
        ∃ mark : Embedding A Target,
          mark.ContainedInIrreducible ∧
          (∀ (a : UA) (ha : alpha a ∈ (↑I : Set P)),
            mark a = f ⟨alpha a, ha⟩) ∧
          (∀ (x : (↑I : Set P)) (a : UA),
            alpha a ∈ (↑I : Set P) →
              (f x = mark a ↔ x.1 = alpha a)) := by
  classical
  let extended : List (Set P) :=
    history ++ singletonProjectedHistory P
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩ :=
    hPrev I hI extended
  have hSingleton : ∀ p : P, Set.singleton p ∈ extended := by
    intro p
    exact List.mem_append.mpr
      (Or.inr (singleton_mem_singletonProjectedHistory p))
  obtain ⟨mark, hContained, hAgree, hTrace⟩ :=
    hCopies.occupied_mark_trace hHist hSingleton alpha
  have hOriginal : SetRespectsProjectedHistory (id : P → P)
      (↑I : Set P) f history := by
    intro K hK x y hxy
    exact hHist K (List.mem_append.mpr (Or.inl hK)) x y hxy
  exact ⟨Z, Target, hTree, f, hWeak, hCopies, hOriginal,
    mark, hContained, hAgree, hTrace⟩

/-- If I contains the entire control placement alpha(A), the
ordinary rank-m predecessor yields a genuinely FULL protected mark.
The parity counterexample shows why this cannot be asserted when
the selected alpha(A) is only partially present. -/
theorem fullAlpha_witness
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} [Fintype P] [DecidableEq P]
    {m : ℕ}
    (hPrev : AtMost A Base D (id : P → P) m)
    (I : Finset P) (hI : I.card ≤ m)
    (alpha : Embedding A D)
    (hAll : ∀ a : UA, alpha a ∈ I)
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : (↑I : Set P) → Z,
        IsAmbientRelativeWeakHE D (↑I : Set P) Target f ∧
        SetAmbientACopyIntersections A D Target (↑I : Set P) f ∧
        SetRespectsProjectedHistory (id : P → P)
          (↑I : Set P) f history ∧
        ∃ mark : Embedding A Target,
          mark.ContainedInIrreducible ∧
          (∀ (x : (↑I : Set P)) (a : UA),
            f x = mark a ↔ x.1 = alpha a) := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist,
    mark, hContained, _hAgree, hTrace⟩ :=
    hPrev.occupiedAlpha_witness I hI alpha history
  refine ⟨Z, Target, hTree, f, hWeak, hCopies, hHist,
    mark, hContained, ?_⟩
  intro x a
  exact hTrace x a (hAll a)

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMost
