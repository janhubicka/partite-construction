import PartiteConstruction.Functional.ActualStageExposedSideOutput

/-!
# Track D: locate every exposed control output at maximal projected rank

The checked sharp native mixed-rank theorem says: either the exact
weak test has a strict functional Base-tree completion, or one
of its occupied selected A-boundaries exposes a control function
output part q outside that SIDE'S projected weak vertex set.

At MAXIMAL projected cardinality |part[S]| = m+1 with |S|<=m+1,
the part projection is injective on the LITERAL test S. Therefore
an exposed q is in one of exactly two geometrically different states:

* EXTERNAL: q is not the part of ANY tested vertex of S;
* CROSS-SIDE: exactly one tested vertex of S has part q,
  and that vertex is outside the side whose A-boundary exposed q.

This is a concrete, equality-sharp dichotomy for real native
partite Systems with arbitrary set-valued operations and arities.
No test is function-closed or enlarged, no total-fibre homomorphism
is assumed, and no missing target B-tree relative extension is
fabricated. The two alternatives may require different repairs.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P V UA : Type v}

/-- An exposed control output part with its exact maximal-rank
LOCATION recorded: absent from all tested vertices, or uniquely
represented by a tested vertex OUTSIDE the offending side. -/
def System.ClassifiedExposedControlOutputAtAlpha
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset V) (Side : Set V) : Prop :=
  ∃ (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Side) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func F (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' Side ∧
      (q ∉ B.part '' (↑S : Set V) ∨
        ∃! z : V, z ∈ S ∧ z ∉ Side ∧ B.part z = q)

/-- Maximal projection rank makes the part projection injective on
the EXACT tested set, not on its generated closure. -/
theorem System.maximalExactTest_part_injective
    (B : System L P V)
    [DecidableEq P]
    (S : Finset V) (m : ℕ)
    (hSize : S.card ≤ m + 1)
    (hMax : (S.image B.part).card = m + 1) :
    S.card = m + 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, B.part x = B.part y → x = y := by
  classical
  have hLe : (S.image B.part).card ≤ S.card :=
    Finset.card_image_le
  have hCard : S.card = m + 1 := by omega
  exact ⟨hCard, Finset.card_image_iff.mp (hMax.trans hCard.symm)⟩

/-- Maximal projected weak rank already consumes the WHOLE exact
vertex budget: adding ANY omitted source vertex y creates exactly
m+2 vertices, while the projected image grows by one part iff its
part was not already represented in S.

If y has the SAME part as a tested opposite-side vertex, the
new vertex causes a projection collision but does not give an
(m)-sized projected predecessor test: the image remains of size
m+1. This pinpoints why neither simply closing S nor simply
using the lower-rank projected-image branch resolves the hard
mixed-root case. No function-closure hull is constructed. -/
theorem System.maximalExactTest_insert_omitted_budget
    (B : System L P V)
    [DecidableEq V] [DecidableEq P]
    (S : Finset V) (m : ℕ)
    (hSize : S.card ≤ m + 1)
    (hMax : (S.image B.part).card = m + 1)
    (y : V) (hy : y ∉ S) :
    (insert y S).card = m + 2 ∧
      ((insert y S).image B.part).card =
        if B.part y ∈ S.image B.part then m + 1 else m + 2 := by
  classical
  have hExact :
      S.card = m + 1 :=
    (B.maximalExactTest_part_injective S m hSize hMax).1
  have hInserted : (insert y S).card = m + 2 := by
    simp [hy, hExact] <;> omega
  refine ⟨hInserted, ?_⟩
  by_cases hPart : B.part y ∈ S.image B.part
  · simp [Finset.image_insert, hPart, hMax]
  · simp [Finset.image_insert, hPart, hMax]

/-- The exact maximal-image dichotomy classifies the output of
EVERY concrete exposed control function tuple. If its output is
not external to S, the UNIQUE representative is outside Side.

This does not say that the representative belongs to the opposite
particular attachment copy, only that it lies outside the offending
side's full image. In a binary free amalgam it must be on the other
side (because the two sides cover the whole source). -/
theorem System.exposedControlOutput_maximal_classified
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    [DecidableEq P]
    (Side : Set V) (S : Finset V) (m : ℕ)
    (hSize : S.card ≤ m + 1)
    (hMax : (S.image B.part).card = m + 1)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha Side) :
    B.ClassifiedExposedControlOutputAtAlpha D alpha S Side := by
  classical
  have hInj :=
    (B.maximalExactTest_part_injective S m hSize hMax).2
  obtain ⟨F, xs, q, hInputs, hControl, hOutside⟩ := hExposed
  refine ⟨F, xs, q, hInputs, hControl, hOutside, ?_⟩
  by_cases hInTest : q ∈ B.part '' (↑S : Set V)
  · right
    obtain ⟨z, hzS, hzq⟩ := hInTest
    refine ⟨z, ⟨hzS, ?_, hzq⟩, ?_⟩
    · intro hzSide
      exact hOutside ⟨z, hzSide, hzq⟩
    · intro y ⟨hyS, _hyNotSide, hyq⟩
      exact hInj y hyS z hzS (hyq.trans hzq.symm)
  · exact Or.inl hInTest

/-- The classified predicate is equivalent to ordinary exposure
when the exact test has maximal projected rank. It records
additional location information, not an extra unsupported
structural or Ramsey assumption. -/
theorem System.classifiedExposed_iff_exposed_of_maximal
    (B : System L P V) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    [DecidableEq P]
    (Side : Set V) (S : Finset V) (m : ℕ)
    (hSize : S.card ≤ m + 1)
    (hMax : (S.image B.part).card = m + 1) :
    B.ClassifiedExposedControlOutputAtAlpha D alpha S Side ↔
      B.ExposedControlOutputAtAlpha D alpha Side := by
  constructor
  · rintro ⟨F, xs, q, hInputs, hControl, hOutside, _hLocation⟩
    exact ⟨F, xs, q, hInputs, hControl, hOutside⟩
  · intro hEx
    exact B.exposedControlOutput_maximal_classified
      D alpha Side S m hSize hMax hEx


/-- Under the exact TWO-SIDE covering property of a full free
amalgam, an exposed control output with a unique tested
representative outside the left side must actually be in the
right-side EXTERIOR (never in the left image or common root).

The output is still the SAME concrete control-function slot F,xs,q.
The classification makes no assumptions on source function
closure, and does not silently supply a compatible target
B-tree extension. -/
theorem System.classifiedExposed_otherSide_of_cover
    {C E F : Type v}
    (B : System L P C) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    (l : E → C) (r : F → C)
    (hCover : ∀ z : C,
      (∃ e : E, z = l e) ∨ (∃ f : F, z = r f))
    (hClassified :
      B.ClassifiedExposedControlOutputAtAlpha D alpha S
        ((↑S : Set C) ∩ Set.range l)) :
    ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range l)) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' ((↑S : Set C) ∩ Set.range l) ∧
      (q ∉ B.part '' (↑S : Set C) ∨
        ∃! z : C, z ∈ S ∧
          (∃ f : F, z = r f) ∧
          (∀ e : E, z ≠ l e) ∧ B.part z = q) := by
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside, hLoc⟩ :=
    hClassified
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_⟩
  rcases hLoc with hExternal | ⟨z, ⟨hzS, hzNotLeft, hzq⟩, hUnique⟩
  · exact Or.inl hExternal
  · right
    have hNotL : ∀ e : E, z ≠ l e := by
      intro e heq
      apply hzNotLeft
      exact ⟨hzS, ⟨e, heq.symm⟩⟩
    have hOther : ∃ f : F, z = r f := by
      rcases hCover z with ⟨e, heq⟩ | ⟨f, heq⟩
      · exact (hNotL e heq).elim
      · exact ⟨f, heq⟩
    refine ⟨z, ⟨hzS, hOther, hNotL, hzq⟩, ?_⟩
    intro y ⟨hyS, _hOther, hyNotL, hyq⟩
    apply hUnique y
    refine ⟨hyS, ?_, hyq⟩
    rintro ⟨_hyS, ⟨e, heq⟩⟩
    exact hyNotL e heq.symm



/-- Every FULL source-side embedding has function-closed image.
Hence a control output part q escaping that side's exact tested
projection cannot have a SOURCE output y INSIDE THE WHOLE TEST S
with part q on the same input tuple xs.

This remains true when q is represented by a unique TESTED vertex
on the OPPOSITE source side: that representative is not the output
of the displayed source function tuple. The source function may
instead be undefined at that tuple, or have outputs outside the
literal test. This is a concrete source-local "phantom or omitted
output" obligation, not the assertion that the entire test's
projected image omits q. -/
theorem System.exposedControlOutput_no_tested_source_value
    {C E : Type v}
    (B : System L P C) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    {Left : Structure L E}
    (iL : Structure.Embedding Left B.toStructure)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha
      ((↑S : Set C) ∩ Set.range iL)) :
    ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range iL)) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' ((↑S : Set C) ∩ Set.range iL) ∧
      (∀ y : C,
        y ∈ B.toStructure.func Func (Subtype.val ∘ xs) →
        y ∈ S → B.part y ≠ q) := by
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside⟩ := hExposed
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_⟩
  have hRange : B.toStructure.IsClosed (Set.range iL) :=
    iL.range_isClosed
  have hArgs : ∀ i : Fin (L.funcArity Func),
      (Subtype.val ∘ xs) i ∈ Set.range iL := by
    intro i
    exact (xs i).2.2
  intro y hy hyS hPart
  apply hOutside
  exact ⟨y, ⟨hyS, hRange Func (Subtype.val ∘ xs)
    hArgs hy⟩, hPart⟩



/-- The exact SOURCE provenance of an exposed native control output
in a full attachment side, under the actual EHN projection.

Either the ENTIRE source function fibre at that input tuple is
UNDEFINED (the genuine domain-reflection failure), or the target
output part q is realized by a UNIQUE value of that SAME source
fibre, lying in the closed attaching side but OUTSIDE the
literal finite tested set S.

The uniqueness is per genuine function fibre and target part,
using the transversal output invariant. It says nothing about
an unrelated opposite-side tested vertex of part q. No closure
hull, total-fibre map on undefined inputs, or new B-tree target
extension is assumed. -/
theorem System.exposedControlOutput_sourceUndefined_or_omittedUnique
    {C E : Type v}
    (B : System L P C) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    {Left : Structure L E}
    (iL : Structure.Embedding Left B.toStructure)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha
      ((↑S : Set C) ∩ Set.range iL)) :
    ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range iL)) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' ((↑S : Set C) ∩ Set.range iL) ∧
      (¬ (B.toStructure.func Func (Subtype.val ∘ xs)).Nonempty ∨
        ∃! y : C,
          y ∈ B.toStructure.func Func (Subtype.val ∘ xs) ∧
          B.part y = q ∧
          y ∈ Set.range iL ∧ y ∉ S) := by
  classical
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside⟩ := hExposed
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_⟩
  let args : Fin (L.funcArity Func) → C := Subtype.val ∘ xs
  by_cases hDefined : (B.toStructure.func Func args).Nonempty
  · right
    have hFibre := hB.map_func_of_nonempty Func args hDefined
    have hq : q ∈ Structure.imageSet B.part (B.toStructure.func Func args) := by
      rw [hFibre]
      exact hControl
    obtain ⟨y, hy, hyq⟩ := hq
    have hRangeClosed : B.toStructure.IsClosed (Set.range iL) :=
      iL.range_isClosed
    have hArgsRange : ∀ i : Fin (L.funcArity Func),
        args i ∈ Set.range iL := by
      intro i
      exact (xs i).2.2
    have hyRange : y ∈ Set.range iL :=
      hRangeClosed Func args hArgsRange hy
    have hyOutside : y ∉ S := by
      intro hyS
      exact hOutside ⟨y, ⟨hyS, hyRange⟩, hyq⟩
    refine ⟨y, ⟨hy, hyq, hyRange, hyOutside⟩, ?_⟩
    intro z ⟨hz, hzq, _, _⟩
    exact B.funcTransversal Func args z y hz hy
      (hzq.trans hyq.symm)
  · exact Or.inl hDefined



/-- Refine the exact EHN source-provenance dichotomy by replacing a
genuinely undefined source function input with an ACTUAL proper FULL
free decomposition of its function-generated input hull.

If the target control requires q but the source fibre is empty,
the previously verified EHN input-hull decomposition theorem applies.
Otherwise q has exactly one source value, and it lies in the
attachment-side image but OUTSIDE the literal weak test.

CRITICAL: The generated input hull here is used only as a
decomposition CERTIFICATE; it is NOT substituted for the weak
tested set S, and NO generator or vertex-rank bound on that hull
is inferred. A history-compatible TARGET root extension remains
unproved. -/
theorem System.exposedControlOutput_reducibleHull_or_omittedUnique
    {C E : Type v}
    (B : System L P C) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    {Left : Structure L E}
    (iL : Structure.Embedding Left B.toStructure)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha
      ((↑S : Set C) ∩ Set.range iL)) :
    ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range iL)) (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' ((↑S : Set C) ∩ Set.range iL) ∧
      (Nonempty (Structure.ProperFreeDecomposition
        (B.toStructure.induce
          (B.toStructure.functionClosure
            (Set.range (Subtype.val ∘ xs)))
          (B.toStructure.functionClosure_isClosed
            (Set.range (Subtype.val ∘ xs))))) ∨
        ∃! y : C,
          y ∈ B.toStructure.func Func (Subtype.val ∘ xs) ∧
          B.part y = q ∧
          y ∈ Set.range iL ∧ y ∉ S) := by
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside, hCase⟩ :=
    B.exposedControlOutput_sourceUndefined_or_omittedUnique
      D hB alpha S iL hExposed
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_⟩
  rcases hCase with hUndefined | hOmitted
  · left
    have hTarget :
        (D.func Func (B.part ∘ (Subtype.val ∘ xs))).Nonempty :=
      ⟨q, hControl⟩
    exact hB.inputHull_reducible_of_domainFailure
      Func (Subtype.val ∘ xs) hTarget hUndefined
  · exact Or.inr hOmitted


end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {UA VB H E F C P : Type v}

/-- Sharp maximal-mixed rank frontier in an ACTUAL functional-partite
free attachment. Either a strict full-functional Base-tree witness
exists for the exact weak test and its entire projected history,
or there is a concrete source-side output event whose part is
EXTERNAL to the whole test or occurs at ONE vertex outside
the offending attaching side.

The predecessor witness, mixedness, source free-amalgam, full
alpha placement and original EHN projection hypotheses are
exactly those of the already checked sharp theorem. -/
theorem System.weakTree_or_classified_exposed_alpha_mixed_succ
    (B : System L P C) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left B.toStructure}
    {iR : Structure.Embedding Right B.toStructure}
    [Fintype UA] [Fintype P] [DecidableEq P] [DecidableEq C]
    [Fintype E] [Fintype F]
    (hSrc : Structure.IsFreeAmalgam sL sR iL iR)
    (alpha : Structure.Embedding A D)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, B.part (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (eAB : Structure.Embedding A Base)
    (hBase : Base.Irreducible)
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (S : Finset C) (hS : S.card ≤ m + 1)
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base B.toStructure B.part (↑S : Set C) history ∨
      ((S.image B.part).card = m + 1 ∧
        (B.ClassifiedExposedControlOutputAtAlpha
            D alpha S ((↑S : Set C) ∩ Set.range iL)
          ∨ B.ClassifiedExposedControlOutputAtAlpha
            D alpha S ((↑S : Set C) ∩ Set.range iR))) := by
  rcases B.weakTree_or_exposed_alpha_side_mixed_succ
      D hB hA hSrc alpha hRootAlpha Base eAB hBase
      m hPrev S hS hMixedL hMixedR history with
      hGood | ⟨hMax, hBad⟩
  · exact Or.inl hGood
  · refine Or.inr ⟨hMax, ?_⟩
    rcases hBad with hLeft | hRight
    · exact Or.inl (B.exposedControlOutput_maximal_classified
        D alpha ((↑S : Set C) ∩ Set.range iL) S m hS hMax hLeft)
    · exact Or.inr (B.exposedControlOutput_maximal_classified
        D alpha ((↑S : Set C) ∩ Set.range iR) S m hS hMax hRight)

end StructuralRamsey.FunctionalPartite
