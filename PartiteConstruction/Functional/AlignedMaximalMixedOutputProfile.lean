import PartiteConstruction.Functional.MaximalMixedExposedOutputLocation

/-!
# Track D: ONE aligned output profile for the maximal native mixed frontier

The earlier actual-stage sharp theorem returns maximal projected
test rank and an exposed output on one source attachment side.
Four independent flags (external/cross-side and undefined/omitted)
are useless for the next rooted completion unless they refer to the
SAME control symbol, SAME source input tuple and SAME output part.

This module packages an aligned four-way certificate:
  • literal projected rank is maximal and injective on exact S;
  • the SAME q is either absent from S or uniquely represented
    outside the exposed side;
  • for the SAME F,x,q, either the input-generated source hull has
    a proper FULL free decomposition (actual EHN domain failure),
    or the genuine source fibre contains a unique output y of
    part q on the exposed side but outside S.

The input hull is a DIAGNOSTIC, not a replacement for the exact
weak test. The selected weak source test is never enlarged.
This result does NOT construct a compatible strict functional
Base-tree target over a hard multi-generated root. It isolates the
one concrete profile that such a construction must handle.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}}
variable {P C UA E : Type v}

/-- The exact aligned source-side profile of ONE exposed operation.
All alternatives refer to one specified (Func, xs, q), rather
than unrelated existential choices. The missing output lies
outside the literal tested source side. -/
def System.AlignedMaximalExposedSourceProfile
    (B : System L P C) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    {Left : Structure L E}
    (iL : Structure.Embedding Left B.toStructure) : Prop :=
  ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range iL))
      (q : P),
    (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
    q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
    q ∉ B.part '' ((↑S : Set C) ∩ Set.range iL) ∧
    (q ∉ B.part '' (↑S : Set C) ∨
      ∃! z : C, z ∈ S ∧
        (∀ e : E, z ≠ iL e) ∧
        B.part z = q) ∧
    (Nonempty (Structure.ProperFreeDecomposition
       (B.toStructure.induce
         (B.toStructure.functionClosure
           (Set.range (Subtype.val ∘ xs)))
         (B.toStructure.functionClosure_isClosed
           (Set.range (Subtype.val ∘ xs))))) ∨
      ∃! y : C,
        y ∈ B.toStructure.func Func (Subtype.val ∘ xs) ∧
        B.part y = q ∧
        y ∈ Set.range iL ∧ y ∉ S)

/-- A *single* EHN-exposed output q in a full native attachment side
admits BOTH precise location and source-domain classifications with
exactly the same operation symbol and source argument tuple.

At maximal |B.part[S]| = m+1 and |S| <= m+1, tested part labels
are injective, giving uniqueness of any cross-side representative.
The source output alternative uses actual EHN fibre exactness and
transversal set-valued output uniqueness, not total-fibre reflection
for undefined tuples. -/
theorem System.alignedMaximalExposedSourceProfile_of_exposed
    (B : System L P C) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    [DecidableEq P]
    (S : Finset C) (m : ℕ)
    (hS : S.card ≤ m + 1)
    (hMax : (S.image B.part).card = m + 1)
    {Left : Structure L E}
    (iL : Structure.Embedding Left B.toStructure)
    (hExposed : B.ExposedControlOutputAtAlpha D alpha
      ((↑S : Set C) ∩ Set.range iL)) :
    B.AlignedMaximalExposedSourceProfile D alpha S iL := by
  classical
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside, hSource⟩ :=
    B.exposedControlOutput_reducibleHull_or_omittedUnique
      D hB alpha S iL hExposed
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_, hSource⟩
  have hInj :=
    (B.maximalExactTest_part_injective S m hS hMax).2
  by_cases hInTest : q ∈ B.part '' (↑S : Set C)
  · right
    obtain ⟨z, hzS, hzq⟩ := hInTest
    have hNoLeft : ∀ e : E, z ≠ iL e := by
      intro e heq
      apply hOutside
      refine ⟨z, ⟨hzS, ⟨e, heq.symm⟩⟩, hzq⟩
    refine ⟨z, ⟨hzS, hNoLeft, hzq⟩, ?_⟩
    intro w ⟨hwS, _hwNoLeft, hwq⟩
    exact hInj w hwS z hzS (hwq.trans hzq.symm)
  · exact Or.inl hInTest


/-- In a real full binary source free amalgam, an aligned
cross-side q-witness from the LEFT side lies specifically in
the RIGHT-SIDE EXTERIOR. Both location and source-fibre origin
remain witnessed by the SAME (Func, xs, q), with the same
test cardinality and no generated closure.

Only the two-side covering property of the genuine full
source free amalgam is used. This is a source-side localization
theorem, not a strict target-tree extension. -/
theorem System.alignedMaximalExposedSourceProfile_otherSide
    {C E F : Type v}
    (B : System L P C) (D : Structure L P)
    {A : Structure L UA}
    (alpha : Structure.Embedding A D)
    (S : Finset C)
    {Left : Structure L E} {Right : Structure L F}
    (iL : Structure.Embedding Left B.toStructure)
    (iR : Structure.Embedding Right B.toStructure)
    (hCover : ∀ z : C,
      (∃ e : E, z = iL e) ∨ (∃ f : F, z = iR f))
    (hProfile :
      B.AlignedMaximalExposedSourceProfile D alpha S iL) :
    ∃ (Func : L.FuncSymbol)
      (xs : Fin (L.funcArity Func) →
        ↥((↑S : Set C) ∩ Set.range iL))
      (q : P),
      (∀ i, B.part (xs i).1 ∈ Set.range alpha) ∧
      q ∈ D.func Func (B.part ∘ (Subtype.val ∘ xs)) ∧
      q ∉ B.part '' ((↑S : Set C) ∩ Set.range iL) ∧
      (q ∉ B.part '' (↑S : Set C) ∨
        ∃! z : C,
          z ∈ S ∧
          (∃ f : F, z = iR f) ∧
          (∀ e : E, z ≠ iL e) ∧
          B.part z = q) ∧
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
  obtain ⟨Func, xs, q, hInputs, hControl, hOutside, hLoc, hOrigin⟩ :=
    hProfile
  refine ⟨Func, xs, q, hInputs, hControl, hOutside, ?_, hOrigin⟩
  rcases hLoc with hExternal | ⟨z, ⟨hzS, hzNotL, hzq⟩, hUnique⟩
  · exact Or.inl hExternal
  · right
    have hOther : ∃ f : F, z = iR f := by
      rcases hCover z with ⟨e, heq⟩ | ⟨f, heq⟩
      · exact (hzNotL e heq).elim
      · exact ⟨f, heq⟩
    refine ⟨z, ⟨hzS, hOther, hzNotL, hzq⟩, ?_⟩
    intro w ⟨hwS, _hwOther, hwNotL, hwq⟩
    exact hUnique w ⟨hwS, hwNotL, hwq⟩


end StructuralRamsey.FunctionalPartite


namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- Exact maximal-mixed native Picture frontier with a SINGLE
coherent four-way output profile.

The first branch is the already checked strict genuine full-
functional Base-tree weak-history witness on the exact source S.
The second branch retains maximal |part[S]| = m+1 and an aligned
F,x,q profile on exactly one of the two actual full attachment
sides. Full ambient A-copy histories and transverse function
fibres are unchanged. The hard relative target extension is
NOT smuggled in as an assumption or conclusion. -/
theorem System.weakTree_or_aligned_exposed_alpha_mixed_succ
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
        (B.AlignedMaximalExposedSourceProfile D alpha S iL
          ∨ B.AlignedMaximalExposedSourceProfile D alpha S iR)) := by
  rcases B.weakTree_or_exposed_alpha_side_mixed_succ
      D hB hA hSrc alpha hRootAlpha Base eAB hBase
      m hPrev S hS hMixedL hMixedR history with
      hGood | ⟨hMax, hExposed⟩
  · exact Or.inl hGood
  · right
    refine ⟨hMax, ?_⟩
    rcases hExposed with hLeft | hRight
    · exact Or.inl
        (B.alignedMaximalExposedSourceProfile_of_exposed
          D hB alpha S m hS hMax iL hLeft)
    · exact Or.inr
        (B.alignedMaximalExposedSourceProfile_of_exposed
          D hB alpha S m hS hMax iR hRight)

end StructuralRamsey.FunctionalPartite
