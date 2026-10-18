import PartiteConstruction.Functional.ClosedOccupiedAMixedGlue

/-!
# Genuine native functional mixed tests: successor-rank side budgets

A mixed exact weak vertex test S of cardinal at most m+1 in an
ACTUAL full functional binary free attachment has both proper side
intersections. Thus each exact projected side weak test has at
most m vertices, without injecting the projection or closing S.

Combining these derived numeric budgets with the existing full
functional closed-occupied-A-boundary mixed-gluing theorem gives
a genuine rank-m -> rank-(m+1) strict Base-tree witness for EVERY
mixed S whose two occupied alpha(A) sets are FUNCTION-CLOSED in A.

The nonclosed occupied-root case remains the history-dependent
target profile existence gap. No universal mixed-stage completion
schema, fixed global A-mark, or total-fibre projection is assumed.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- The direct successor-cardinal version of the verified native
functional closed-root mixed rank increment.

Unlike the preceding weakTree_of_closedOccupied_alpha_sides,
the projected side size bounds are NOT additional hypotheses:
they follow from exact finite-cardinality and genuine mixedness.
The conclusion preserves all surviving multivalued function fibres,
all actual ambient full A-copy intersections, and arbitrary finite
projected histories in a STRICT full-functional B-tree.

The closedness hypotheses concern only the OCCUPIED alpha(A)
boundaries, not the whole weak S or the full source sides. -/
theorem weakTree_of_closedOccupied_alpha_mixed_succ
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype UA] [Fintype P] [DecidableEq P] [DecidableEq C]
    [Fintype E] [Fintype F]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (p : C → P)
    (hp : Whole.IsEHNHomomorphismEmbedding D p)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, p (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (eAB : Embedding A Base) (hBase : Base.Irreducible)
    (m : ℕ)
    (hPrev : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base D (id : P → P) m)
    (S : Finset C) (hS : S.card ≤ m + 1)
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f)
    (hClosedL : A.IsClosed {a : UA |
      alpha a ∈ ((↑(Finset.image (p ∘ iL)
          ((Finset.univ : Finset E).filter (fun e => iL e ∈ S)))) : Set P)})
    (hClosedR : A.IsClosed {a : UA |
      alpha a ∈ ((↑(Finset.image (p ∘ iR)
          ((Finset.univ : Finset F).filter (fun f => iR f ∈ S)))) : Set P)})
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) history := by
  classical
  let SL : Finset E :=
    Finset.univ.filter (fun e => iL e ∈ S)
  let SR : Finset F :=
    Finset.univ.filter (fun f => iR f ∈ S)
  have hSmallL : SL.card < S.card := by
    obtain ⟨z, hz, hOutside⟩ := hMixedL
    let T : Finset C := SL.image iL
    have hSubset : T ⊆ S := by
      intro w hw
      change w ∈ SL.image iL at hw
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hw
      rw [← heq]
      exact (Finset.mem_filter.mp he).2
    have hzNot : z ∉ T := by
      intro hzT
      change z ∈ SL.image iL at hzT
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hzT
      exact hOutside e heq.symm
    have hProper : T ⊂ S := by
      apply Finset.ssubset_iff.mpr
      refine ⟨z, hzNot, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hz
      · exact hSubset hw
    have hCardImage : T.card = SL.card :=
      Finset.card_image_iff.mpr
        (fun _ _ _ _ h => iL.injective h)
    rw [← hCardImage]
    exact Finset.card_lt_card hProper
  have hSmallR : SR.card < S.card := by
    obtain ⟨z, hz, hOutside⟩ := hMixedR
    let T : Finset C := SR.image iR
    have hSubset : T ⊆ S := by
      intro w hw
      change w ∈ SR.image iR at hw
      obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hw
      rw [← heq]
      exact (Finset.mem_filter.mp hf).2
    have hzNot : z ∉ T := by
      intro hzT
      change z ∈ SR.image iR at hzT
      obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hzT
      exact hOutside f heq.symm
    have hProper : T ⊂ S := by
      apply Finset.ssubset_iff.mpr
      refine ⟨z, hzNot, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hz
      · exact hSubset hw
    have hCardImage : T.card = SR.card :=
      Finset.card_image_iff.mpr
        (fun _ _ _ _ h => iR.injective h)
    rw [← hCardImage]
    exact Finset.card_lt_card hProper
  have hCardL : (SL.image (p ∘ iL)).card ≤ m := by
    have hImage : (SL.image (p ∘ iL)).card ≤ SL.card :=
      Finset.card_image_le
    omega
  have hCardR : (SR.image (p ∘ iR)).card ≤ m := by
    have hImage : (SR.image (p ∘ iR)).card ≤ SR.card :=
      Finset.card_image_le
    omega
  exact hSrc.weakTree_of_closedOccupied_alpha_sides hA
    D alpha p hp hRootAlpha Base eAB hBase m hPrev S
    hCardL hCardR hClosedL hClosedR history

end StructuralRamsey.Structure.IsFreeAmalgam
