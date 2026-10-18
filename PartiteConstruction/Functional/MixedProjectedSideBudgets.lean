import PartiteConstruction.Functional.ClosedOccupiedAMixedGlue

/-!
# Reusable projected-side cardinal budgets for genuine mixed functional attachments

If S is an EXACT finite test of size at most m+1 and each of
two FULL side embeddings omits at least one tested vertex,
the literal side preimages have STRICTLY fewer tested vertices
than S, by injectivity and proper subset cardinality.

Consequently ANY function p from the ambient carrier to a
projected control has side images of size at most m. The
projection is not assumed to be injective, total-fibre,
EHN, or even a homomorphism for this NUMERICAL lemma.

Extracts the earlier duplicated cardinal arithmetic in
ClosedOccupiedAMixedRankSucc into an independent interface
that both weak-predecessor and closed-only-predecessor
native functional mixed steps can reuse. No weak set
is closed or enlarged to a generated hull.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {E F C P : Type v}

/-- Automatic exact projected-side budgets for two injective
source-side embeddings whose images both omit a tested point.

No source free-amalgamation or functional projection axioms
are needed for this purely finite combinatorial calculation. -/
theorem projectedSideBudgets_of_mixed
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    (iL : Embedding Left Whole) (iR : Embedding Right Whole)
    [Fintype E] [Fintype F] [DecidableEq C] [DecidableEq P]
    (p : C → P) (m : ℕ)
    (S : Finset C) (hS : S.card ≤ m + 1)
    (hMixedL : ∃ z : C, z ∈ S ∧ ∀ e : E, z ≠ iL e)
    (hMixedR : ∃ z : C, z ∈ S ∧ ∀ f : F, z ≠ iR f) :
    (Finset.image (p ∘ iL)
      ((Finset.univ : Finset E).filter (fun e => iL e ∈ S))).card ≤ m ∧
    (Finset.image (p ∘ iR)
      ((Finset.univ : Finset F).filter (fun f => iR f ∈ S))).card ≤ m := by
  classical
  let SL : Finset E := Finset.univ.filter (fun e => iL e ∈ S)
  let SR : Finset F := Finset.univ.filter (fun f => iR f ∈ S)
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
  exact ⟨hCardL, hCardR⟩

end StructuralRamsey.Structure
