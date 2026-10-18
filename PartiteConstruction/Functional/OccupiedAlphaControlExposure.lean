import PartiteConstruction.Functional.ControlMissingClosedRankSplit

/-!
# Occupied selected A-boundaries and escaping functional control values

Fix a genuine FULL embedding alpha:A↪D and a native functional
partite System B over the carrier of D. For an arbitrary EXACT weak
vertex set S of B, the occupied selected A-boundary is

  H = {a : A | alpha a ∈ B.part '' S}.

Its being function-closed is equivalent to the ABSENCE of an
exposed control-output obligation: a D-function tuple on input
parts represented by S with an output q NOT represented in S.

The equivalence needs only alpha full, not that B.part is a full
homomorphism, an EHN map, or globally injective. In particular it
handles multivalued functions, repeated inputs, nullaries and weak
nonclosed S, with no closure-hull/rank inflation.

If S is itself function-closed and B is EHN-partite over D, an
exposed slot is necessarily a source-undefined CONTROL output.
The previously verified closed-test rank-split lemma decomposes
the ENTIRE induced finite source test into proper full functional
free-amalgam sides of strictly smaller vertex cardinalities.

This identifies the exact remaining obstacle to the strict
functional weak-vertex iteration: intermediate S need not be
closed, so this reducibility shortcut cannot replace a compatible
history-dependent TARGET B-tree root completion.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P V UA : Type v}

/-- A selected A-output-root exposed by an exact weak source test:
all input parts are occupied in alpha(A), a real control value
q exists, but q is outside the tested projection B.part '' S.

The actual source function need not be defined at these inputs.
This predicate does NOT assert domain-reflection of B.part. -/
def System.ExposedControlOutputAtAlpha
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Set V) : Prop :=
  ∃ (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func F (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' S

/-- The OCCUPIED alpha(A)-boundary is function-closed precisely
when there are NO control function outputs escaping the exact
projected weak test. Fullness of alpha is essential to the
reverse implication. No EHN hypothesis on the source is needed. -/
theorem System.occupiedAlphaClosed_iff_noExposed
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D) (S : Set V) :
    A.IsClosed {a : UA | alpha a ∈ B.part '' S} ↔
      ¬ B.ExposedControlOutputAtAlpha D alpha S := by
  classical
  constructor
  · intro hClosed hExposed
    obtain ⟨F, xs, q, hInputs, hControl, hOutside⟩ := hExposed
    have hLift :
        ∀ i : Fin (L.funcArity F),
          ∃ a : UA, alpha a = B.part (xs i).1 := by
      intro i
      exact hInputs i
    choose args hArgs using hLift
    have hEq :
        B.part ∘ (Subtype.val ∘ xs) = alpha ∘ args := by
      funext i
      exact (hArgs i).symm
    have hValue :
        q ∈ D.func F (alpha ∘ args) := by
      simpa only [hEq] using hControl
    have hImage :
        q ∈ imageSet alpha (A.func F args) := by
      rw [alpha.map_func F args]
      exact hValue
    obtain ⟨b, hb, hbq⟩ := hImage
    have hArgsOccupied : ∀ i, args i ∈
        {a : UA | alpha a ∈ B.part '' S} := by
      intro i
      change alpha (args i) ∈ B.part '' S
      rw [hArgs i]
      exact ⟨(xs i).1, (xs i).2, rfl⟩
    have hbOccupied : b ∈
        {a : UA | alpha a ∈ B.part '' S} :=
      hClosed F args hArgsOccupied hb
    have hqOccupied : q ∈ B.part '' S := by
      change alpha b ∈ B.part '' S at hbOccupied
      rw [hbq] at hbOccupied
      exact hbOccupied
    exact hOutside hqOccupied
  · intro hNo F args hArgs b hb
    by_contra hbOutside
    have hLift :
        ∀ i : Fin (L.funcArity F),
          ∃ x : S, B.part x.1 = alpha (args i) := by
      intro i
      have hi : alpha (args i) ∈ B.part '' S := hArgs i
      obtain ⟨x, hxS, hxPart⟩ := hi
      exact ⟨⟨x, hxS⟩, hxPart⟩
    choose xs hXs using hLift
    have hInputEq :
        B.part ∘ (Subtype.val ∘ xs) = alpha ∘ args := by
      funext i
      exact hXs i
    have hValue :
        alpha b ∈ D.func F
          (B.part ∘ (Subtype.val ∘ xs)) := by
      rw [hInputEq, ← alpha.map_func F args]
      exact ⟨b, hb, rfl⟩
    have hbNotIn : alpha b ∉ B.part '' S := hbOutside
    apply hNo
    refine ⟨F, xs, alpha b, ?_, hValue, hbNotIn⟩
    intro i
    exact ⟨args i, (hXs i).symm⟩

/-- If the occupied selected A-boundary is not closed, there is
a CONCRETE escaping output q in the control over an input tuple
whose parts are represented inside the exact weak test. -/
theorem System.exposed_of_not_occupiedAlphaClosed
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D) (S : Set V)
    (hNotClosed :
      ¬ A.IsClosed {a : UA | alpha a ∈ B.part '' S}) :
    B.ExposedControlOutputAtAlpha D alpha S := by
  classical
  by_contra hNo
  exact hNotClosed
    ((B.occupiedAlphaClosed_iff_noExposed D alpha S).mpr hNo)

/-- Each escaping projected control value is an actual
control-missing output-part slot: since q is outside B.part '' S,
there cannot be any surviving weak function output of part q.
The input-part alpha labels are retained for relative-history use. -/
theorem System.exposed_has_controlMissing
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D) (S : Set V)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha S) :
    ∃ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → S) (q : P),
        (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
        q ∉ B.part '' S ∧
        B.ControlMissingAtPart D S F xs q := by
  obtain ⟨F, xs, q, hInputs, hControl, hOutside⟩ := hExposed
  refine ⟨F, xs, q, hInputs, hOutside, ⟨hControl, ?_⟩⟩
  rintro ⟨y, hy, hPart⟩
  have hyPart : B.part y.1 ∈ B.part '' S :=
    ⟨y.1, y.2, rfl⟩
  apply hOutside
  rw [← hPart]
  exact hyPart

/-- A nonclosed occupied A-boundary of a GENUINELY CLOSED finite
source test under EHN control yields a proper FULL free decomposition
of the WHOLE exact induced test, with three strict cardinal drops.

No generated closure of the finite test or projected test appears. -/
theorem System.not_occupiedAlphaClosed_closedFiniteTest_decompose
    (B : System L P V) (D : Structure L P)
    [Finite V]
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset V)
    (hClosed : B.toStructure.IsClosed (↑S : Set V))
    (hNotClosed :
      ¬ A.IsClosed
        {a : UA | alpha a ∈ B.part '' (↑S : Set V)}) :
    let Small := B.toStructure.induce (↑S : Set V) hClosed
    ∃ d : ProperFreeDecomposition Small,
      Nat.card d.Left < Nat.card ↥(↑S : Set V) ∧
      Nat.card d.Right < Nat.card ↥(↑S : Set V) ∧
      Nat.card d.Common < Nat.card ↥(↑S : Set V) := by
  obtain ⟨F, xs, q, _, _, hMissing⟩ :=
    B.exposed_has_controlMissing D alpha (↑S : Set V)
      (B.exposed_of_not_occupiedAlphaClosed
        D alpha (↑S : Set V) hNotClosed)
  exact B.controlMissing_closedFiniteTest_decompose
    D hB S hClosed F xs q hMissing

/-- Equivalently: if the exact induced CLOSED finite source test
is irreducible, every occupied selected FULL A-copy boundary is
function-closed. This does NOT apply to arbitrary weak nonclosed
tests in the actual rank-increment recursion. -/
theorem System.occupiedAlphaClosed_of_closedFinite_irreducible
    (B : System L P V) (D : Structure L P)
    [Finite V]
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset V)
    (hClosed : B.toStructure.IsClosed (↑S : Set V))
    (hIrr :
      (B.toStructure.induce (↑S : Set V) hClosed).Irreducible) :
    A.IsClosed
      {a : UA | alpha a ∈ B.part '' (↑S : Set V)} := by
  classical
  by_contra hBad
  obtain ⟨d, _, _, _⟩ :=
    B.not_occupiedAlphaClosed_closedFiniteTest_decompose
      D hB alpha S hClosed hBad
  exact hIrr.noProperFreeDecomposition ⟨d⟩

end StructuralRamsey.FunctionalPartite
