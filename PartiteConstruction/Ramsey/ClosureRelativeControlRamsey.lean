import PartiteConstruction.Ramsey.ClosureProtectedInitial
import PartiteConstruction.Ramsey.ClosureRelativeControlPicture

/-! # End-to-end closed-test Ramsey construction with relative A-copies

This proves the closed-test version of the relative-copy hypothesis in
Lemma 2.29: all A-copies in the control are relative U-substructures.
The control need not be closed. The initial picture, whole finite pass,
and final global Ramsey extraction are all constructed.

The rank-one corollary supplies actual rank-one Ramsey witnesses. The
last theorem proves the corrected local-finiteness implication when its
cutoff is at most one. Neither a higher-rank increment nor the arbitrary
nonclosed-control version of Lemma 2.28 is asserted.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V P W : Type v}

/-- Canonical colouring on the native initial picture extracts the
GLOBAL Ramsey arrow, not merely one colour for each projection profile. -/
theorem arrow_of_initial_canonical
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    [Nonempty (RelStructure.Embedding B D)]
    (C : System L P W) (Color : Type*) [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color)
    (hCanon : CanonicalOn A (initialStage B D).system C
      (projectionProfiles A B D (allRelevant A B D)) Color) :
    StructuralRamsey.Arrow A B C.toRelStructure Color := by
  classical
  intro chi
  obtain ⟨f, hf⟩ := hCanon chi
  let P0 := (initialStage B D).system
  let lift (alpha : RelStructure.Embedding A D) (ha : Relevant A B D alpha) :
      ProjectedEmbedding A P0 alpha.toFunctionEmbedding := by
    let beta : RelStructure.Embedding B D := Classical.choose ha
    have hRest : ∃ e : RelStructure.Embedding A B, alpha = beta.comp e :=
      Classical.choose_spec ha
    let e : RelStructure.Embedding A B := Classical.choose hRest
    have he : alpha = beta.comp e := Classical.choose_spec hRest
    refine ⟨(Partite.Initial.copyEmbedding B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding) beta).comp e, ?_⟩
    intro x
    change beta (e x) = alpha x
    rw [he]
    rfl
  let theta : RelStructure.Embedding A D → Color := fun alpha =>
    if ha : Relevant A B D alpha then chi (f.toEmbedding.comp (lift alpha ha).val)
    else Classical.choice (inferInstance : Nonempty Color)
  have hTheta (alpha : RelStructure.Embedding A D) (ha : Relevant A B D alpha)
      (e : ProjectedEmbedding A P0 alpha.toFunctionEmbedding) :
      theta alpha = chi (f.toEmbedding.comp e.val) := by
    simp only [theta, dite_eq_left ha]
    let r : RelevantEmbedding A B D := ⟨alpha, ha⟩
    have hr : r ∈ allRelevant A B D := mem_allRelevant A B D r
    have hp : alpha.toFunctionEmbedding ∈
        projectionProfiles A B D (allRelevant A B D) :=
      List.mem_map.mpr ⟨r, hr, rfl⟩
    exact hf alpha.toFunctionEmbedding hp (lift alpha ha) e
  obtain ⟨beta, hBeta⟩ := hArrow theta
  let j : RelStructure.Embedding B P0.toRelStructure :=
    Partite.Initial.copyEmbedding B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding) beta
  refine ⟨f.toEmbedding.comp j, ?_⟩
  intro e1 e2
  have ha1 : Relevant A B D (beta.comp e1) := ⟨beta, e1, rfl⟩
  have ha2 : Relevant A B D (beta.comp e2) := ⟨beta, e2, rfl⟩
  have h := hBeta e1 e2
  rw [hTheta (beta.comp e1) ha1 (initialProjectedCopy (A := A) B D beta e1),
    hTheta (beta.comp e2) ha2 (initialProjectedCopy (A := A) B D beta e2)] at h
  have hj1 : (initialProjectedCopy (A := A) B D beta e1).val = j.comp e1 := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have hj2 : (initialProjectedCopy (A := A) B D beta e2).val = j.comp e2 := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  rw [hj1, hj2] at h
  rw [RelStructure.Embedding.comp_assoc, RelStructure.Embedding.comp_assoc]
  exact h

/-- Constructed closed-test Ramsey witness when every A-copy of D is
relative U-closed. D itself may have missing or conflicting closures.
Coverage is by the original B, not by the much larger initial picture. -/
theorem closed_ramsey_of_relative_A_copies
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (eAB : RelStructure.Embedding A B)
    (hCopies : ∀ alpha : RelStructure.Embedding A D,
      IsUSubstructure rules D (Set.range alpha))
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color) :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      StructuralRamsey.Arrow A B C.toRelStructure Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B)) := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D Color hArrow
  let S0 := (initialStage B D).system
  let beta : RelStructure.Embedding B D := Classical.choice inferInstance
  let a0 : RelStructure.Embedding A S0.toRelStructure :=
    (Partite.Initial.copyEmbedding B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding) beta).comp eAB
  have hS0 : IsUClosed rules S0.toRelStructure :=
    Initial.picture_isUClosed B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding) hB
  have hS0Part : IsClosedUHomomorphismEmbedding rules S0.toRelStructure D S0.part :=
    Initial.picture_isClosedPartiteOver B D (fun gamma : RelStructure.Embedding B D => gamma)
  let profiles := (allRelevant A B D).map (fun alpha => alpha.1)
  obtain ⟨Y, hY, C, hCanon, hC, hCPart, hCCover⟩ :=
    protected_pass_of_relative_profiles A D S0 hA hS0 hS0Part a0 profiles
      (fun alpha _ => hCopies alpha) Color
  have hCanon' : CanonicalOn A S0 C
      (projectionProfiles A B D (allRelevant A B D)) Color := by
    simpa only [profiles, projectionProfiles, List.map_map, Function.comp_def] using hCanon
  refine ⟨Y, hY, C, arrow_of_initial_canonical A B D C Color hArrow hCanon',
    hC, hCPart, ?_⟩
  intro Z Test hClosed hIrred e
  obtain ⟨d⟩ := hCCover Test hClosed hIrred e
  obtain ⟨i, g, hg⟩ := Initial.closed_test_factor_copy B
    (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding)
    Test hClosed hIrred d
  exact ⟨g⟩

/-- In particular a CLOSED control satisfies the relative-copy
hypothesis automatically. This now includes the initial picture and
GLOBAL Ramsey arrow, which the standalone finite-pass theorem did not. -/
theorem closed_ramsey_of_closed_control
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B) (hD : IsUClosed rules D)
    (eAB : RelStructure.Embedding A B)
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color) :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      StructuralRamsey.Arrow A B C.toRelStructure Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B)) :=
  closed_ramsey_of_relative_A_copies A B D hA hB eAB
    (fun alpha => alpha.range_isUSubstructure hA hD) Color hArrow

/-- A genuine end-to-end case of the repaired local-completion theorem:
cutoff at most one, with relative A-copies in the original control.
There is NO assumed rank-controlled Ramsey witness in this theorem. -/
theorem ramsey_of_closedLocalCompletion_cutoff_one
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBIrr : B.Irreducible) (hKB : K B) (hD : D.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (eAB : RelStructure.Embedding A B)
    (hCopies : ∀ alpha : RelStructure.Embedding A D,
      IsUSubstructure rules D (Set.range alpha))
    (n : ℕ) (hn : n ≤ 1) (hLocal : ClosedULocalCompletionAt K rules B D n)
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color) :
    ∃ (Y : Type v) (_ : Finite Y) (Target : RelStructure L Y),
      K Target ∧ StructuralRamsey.Arrow A B Target Color := by
  obtain ⟨Y, hY, C, hRamsey, hC, hPart, hCover⟩ :=
    closed_ramsey_of_relative_A_copies A B D hA hB eAB hCopies Color hArrow
  letI : Finite Y := hY
  apply ramsey_of_closedLocalCompletionAt_rank_and_coverage
    A B D C.toRelStructure n Color hLocal hHer hKB hC hD C.part hPart hCover
    ?_ hRamsey
  intro S hS hClosed hRank
  exact closed_rank_one_completions_of_protected_coverage hKB hBIrr hCover
    S hClosed (hRank.trans hn)

end StructuralRamsey.Partite.Induced
