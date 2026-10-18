import PartiteConstruction.Functional.SharpMixedRankFrontier
import PartiteConstruction.Functional.OccupiedAlphaControlExposure

/-!
# Native functional mixed stage: strict completion or exposed side output

We combine the checked sharp mixed-rank theorem with the checked
occupied-alpha closure/exposed-output criterion inside ONE ACTUAL
genuine transversal partite System, NOT in a relational surrogate.

For every actual finite weak mixed test of ≤m+1 vertices:
either obtain a strict genuine full-functional Base-tree witness
including ambient A-copy intersections and projected histories,
or the test has maximal projected size m+1 and an actual side
weak test S∩range iX exposes a control function output q outside
that SIDE'S exact projected image.

The escaping q MAY be represented in the opposite side of the
whole weak test. No stronger 'outside p[S]' assertion is made.
The theorem makes NO claim that nonclosed occupied A-boundaries
have a common compatible strict TARGET B-tree completion.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- For an ACTUAL native partite functional full free attachment
whose whole system is B, the only remaining maximal-rank mixed
obstruction has a CONCRETE control-output tuple on one of the
literal side weak subsets S∩range iL or S∩range iR.

The source weak vertex set and projected cardinality are EXACT;
the strict completion alternative retains all history and full
ambient A-copy intersection certificates. -/
theorem System.weakTree_or_exposed_alpha_side_mixed_succ
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
        (B.ExposedControlOutputAtAlpha D alpha
            ((↑S : Set C) ∩ Set.range iL)
         ∨ B.ExposedControlOutputAtAlpha D alpha
            ((↑S : Set C) ∩ Set.range iR))) := by
  classical
  let SL : Finset E :=
    Finset.univ.filter (fun e => iL e ∈ S)
  let SR : Finset F :=
    Finset.univ.filter (fun f => iR f ∈ S)
  let SideL : Set C := (↑S : Set C) ∩ Set.range iL
  let SideR : Set C := (↑S : Set C) ∩ Set.range iR
  have hProjL :
      B.part '' SideL =
        (↑(SL.image (B.part ∘ iL)) : Set P) := by
    ext q
    constructor
    · rintro ⟨x, ⟨hxS, hxRange⟩, hxPart⟩
      obtain ⟨e, rfl⟩ := hxRange
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr
          ⟨Finset.mem_univ e, hxS⟩, hxPart⟩
    · intro hq
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hq
      exact ⟨iL e,
        ⟨(Finset.mem_filter.mp he).2, ⟨e, rfl⟩⟩, heq⟩
  have hProjR :
      B.part '' SideR =
        (↑(SR.image (B.part ∘ iR)) : Set P) := by
    ext q
    constructor
    · rintro ⟨x, ⟨hxS, hxRange⟩, hxPart⟩
      obtain ⟨f, rfl⟩ := hxRange
      exact Finset.mem_image.mpr
        ⟨f, Finset.mem_filter.mpr
          ⟨Finset.mem_univ f, hxS⟩, hxPart⟩
    · intro hq
      obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hq
      exact ⟨iR f,
        ⟨(Finset.mem_filter.mp hf).2, ⟨f, rfl⟩⟩, heq⟩
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part :=
    hB
  have hSharp :=
    hSrc.weakTree_or_maximal_nonclosed_alpha_mixed_succ
      hA D alpha B.part hp hRootAlpha Base eAB hBase
      m hPrev S hS hMixedL hMixedR history
  rcases hSharp with hGood | ⟨hMax, hBad⟩
  · exact Or.inl hGood
  · refine Or.inr ⟨hMax, ?_⟩
    rcases hBad with hBadL | hBadR
    · have hBadSide : ¬ A.IsClosed
          {a : UA | alpha a ∈ B.part '' SideL} := by
        rw [hProjL]
        exact hBadL
      exact Or.inl
        (B.exposed_of_not_occupiedAlphaClosed D alpha SideL hBadSide)
    · have hBadSide : ¬ A.IsClosed
          {a : UA | alpha a ∈ B.part '' SideR} := by
        rw [hProjR]
        exact hBadR
      exact Or.inr
        (B.exposed_of_not_occupiedAlphaClosed D alpha SideR hBadSide)

end StructuralRamsey.FunctionalPartite
