import PartiteConstruction.Functional.ProtectedAMarkWeakPullback
import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue

/-!
# Corrected strict functional MIXED rank increment from protected predecessor

Let Whole be a genuine FULL functional free amalgam of Left and Right
over Root, with global EHN map to the previous control D and with the
FULL source root projecting into one selected full A-placement alpha.

A genuinely mixed finite exact weak vertex test S of size ≤ n meets
both sides outside the overlap. The literal side subsets have fewer
than n tested vertices. The rank-(n−1) *protected-A* strict weak-tree
invariant on the CONTROL D can therefore be pulled back through
the two EHN side part maps. Their marked A-copies have the same
alpha labels and the exact protected trace needed by the already
checked mixed weak-tree gluing theorem.

The result is one genuine STRICT full-functional Base-tree witness for
the original exact S, with ambient-full-A-copy protection and arbitrary
projected histories. No generated closure, no singleton operation,
no reflection of undefined domains, and no universal arbitrary-stage
relative-extension assumption is used.

The C5 arbitrary-stage obstruction does NOT apply: its D=K5 does not
satisfy the rank-4 protected predecessor premise. The genuine
multi-line C7 has rank-deficient projected image and its D=K3 does not
satisfy rank-6 predecessor.

This theorem handles the MIXED branch. Pure-side ambient-A-history
transport still needs separate care; it is not hidden as a hypothesis
or falsely inferred from side completeness alone.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- A genuinely mixed exact weak n-vertex test of a FULL functional
free attachment has a strict functional Base-tree witness, provided
the PREDECESSOR control has protected marked-A witnesses at rank
n−1 for the selected alpha. The mixed side subsets are the exact
preimages, with no closure augmentation.

This is a mathematically stronger and sound replacement for the
false arbitrary-stage `MaximalMixedHardRootSchemaFromTwo` premise:
the actual previous-control rank certificate is visible. -/
theorem mixedWeakTree_of_predecessor_protected
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite E] [Finite F] [DecidableEq P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (p : C → P)
    (hp : Whole.IsEHNHomomorphismEmbedding D p)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, p (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (n : ℕ)
    (hPred : AtMostProtectedWeakTreeWitness
      A Base alpha D (id : P → P) (n - 1))
    (S : Finset C) (hS : S.card ≤ n)
    (hNotLeft : ∃ z : C, z ∈ S ∧ z ∉ Set.range iL)
    (hNotRight : ∃ z : C, z ∈ S ∧ z ∉ Set.range iR)
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p (↑S : Set C) history := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  let pL : E → P := p ∘ iL
  let pR : F → P := p ∘ iR
  have hpL : Left.IsEHNHomomorphismEmbedding D pL :=
    hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : Right.IsEHNHomomorphismEmbedding D pR :=
    hp.comp iR.isEHNHomomorphismEmbedding
  have hPrevL : AtMostProtectedWeakTreeWitness
      A Base alpha Left pL (n - 1) :=
    AtMostProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pL (id : P → P) pL hpL (fun _ => rfl)
      hA (n - 1) hPred
  have hPrevR : AtMostProtectedWeakTreeWitness
      A Base alpha Right pR (n - 1) :=
    AtMostProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pR (id : P → P) pR hpR (fun _ => rfl)
      hA (n - 1) hPred
  let SL : Finset E := Finset.univ.filter (fun a => iL a ∈ S)
  let SR : Finset F := Finset.univ.filter (fun b => iR b ∈ S)
  have hSLset : (↑SL : Set E) = iL ⁻¹' (↑S : Set C) := by
    ext a
    simp [SL]
  have hSRset : (↑SR : Set F) = iR ⁻¹' (↑S : Set C) := by
    ext b
    simp [SR]
  have hSLbound : SL.card ≤ n - 1 := by
    obtain ⟨z, hzS, hzOut⟩ := hNotLeft
    have hSubset : (SL.image iL) ⊆ S.erase z := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      have haS : iL a ∈ S := (Finset.mem_filter.mp ha).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, haS⟩
      intro hEq
      apply hzOut
      exact ⟨a, hEq⟩
    calc
      SL.card = (SL.image iL).card :=
        (Finset.card_image_of_injective SL iL.injective).symm
      _ ≤ (S.erase z).card := Finset.card_le_card hSubset
      _ = S.card - 1 := Finset.card_erase_of_mem hzS
      _ ≤ n - 1 := by omega
  have hSRbound : SR.card ≤ n - 1 := by
    obtain ⟨z, hzS, hzOut⟩ := hNotRight
    have hSubset : (SR.image iR) ⊆ S.erase z := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hbS : iR b ∈ S := (Finset.mem_filter.mp hb).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, hbS⟩
      intro hEq
      apply hzOut
      exact ⟨b, hEq⟩
    calc
      SR.card = (SR.image iR).card :=
        (Finset.card_image_of_injective SR iR.injective).symm
      _ ≤ (S.erase z).card := Finset.card_le_card hSubset
      _ = S.card - 1 := Finset.card_erase_of_mem hzS
      _ ≤ n - 1 := by omega
  have hLeft : SetAmbientProtectedWeakTreeWitness A Base alpha Left
      pL (iL ⁻¹' (↑S : Set C)) history := by
    have h := hPrevL SL hSLbound history
    rw [hSLset] at h
    exact h
  have hRight : SetAmbientProtectedWeakTreeWitness A Base alpha Right
      pR (iR ⁻¹' (↑S : Set C)) history := by
    have h := hPrevR SR hSRbound history
    rw [hSRset] at h
    exact h
  obtain ⟨ZL, TL, hTreeL, fL, hWeakL, hCopiesL, hHistL,
    markL, hcL, hTraceL⟩ := hLeft
  obtain ⟨ZR, TR, hTreeR, fR, hWeakR, hCopiesR, hHistR,
    markR, hcR, hTraceR⟩ := hRight
  exact IsFreeAmalgam.protectedAMarkWeakTree_glue hA hSrc
    (↑S : Set C) alpha p pL pR (fun _ => rfl) (fun _ => rfl)
    hRootAlpha Base TL TR hTreeL hTreeR markL markR hcL hcR
    fL fR hWeakL hWeakR hTraceL hTraceR
    hCopiesL hCopiesR history hHistL hHistR

end StructuralRamsey.Structure.IsFreeAmalgam
