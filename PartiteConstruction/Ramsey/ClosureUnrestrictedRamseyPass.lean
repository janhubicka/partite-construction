import PartiteConstruction.Ramsey.ClosureUnrestrictedPictureStep
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey

/-! # Finite unrestricted closed-test Ramsey passes over nonclosed controls

The repaired local Picture lemma is now constructed over arbitrary
controls, but the nontrivial local refinement requires one actual
selected-profile A-copy in the old picture. For a finite pass, it
suffices that every listed profile have such a copy in the INITIAL
picture. Any Ramsey witness for the previous tail pass includes a
part-preserving copy of the old picture, so these witnesses persist.

For the canonical initial picture indexed by all B->D embeddings,
EVERY relevant A->D profile has such a selected A-copy; relevance
provides the explicit factorization through B. Consequently the
whole finite pass and the global B-Ramsey extraction now work over
an ARBITRARY possibly nonclosed control D. This completes the
closed-test structural/Ramsey witness construction without the
relative-A-copy assumption required in the earlier restricted theorem.

The j-to-j+1 completion-rank increment remains a separate task.
No completion-in-K theorem is inferred merely from the construction.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V P : Type v}

/-- Iterate the ACTUAL unrestricted local protected Picture theorem
over all listed profiles. Every profile must have at least one real
projected A-copy in the INITIAL picture. The supplied witnesses are
transported into every subsequent stage by its copy of the old one.

Closedness, protected projection into the SAME possibly nonclosed D,
and embeddability of all closed U-irreducible tests back into the
ORIGINAL initial picture are preserved throughout the pass. -/
theorem unrestricted_protected_pass
    {rules : ClosureDescription L}
    (A : RelStructure L U) (D : RelStructure L P)
    (B : System L P V)
    (hA : IsUClosed rules A)
    (hB : IsUClosed rules B.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    [Finite U] [Finite V]
    (profiles : List (RelStructure.Embedding A D))
    (hProfiles : ∀ alpha ∈ profiles,
      Nonempty (Partite.ProjectedEmbedding A B alpha.toFunctionEmbedding))
    (Color : Type*) [Fintype Color] [Nonempty Color] :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      CanonicalOn A B C (profiles.map (fun a => a.toFunctionEmbedding)) Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  classical
  induction profiles with
  | nil =>
      refine ⟨V, inferInstance, B, ?_, hB, hPart, ?_⟩
      · intro chi
        exact ⟨Partite.Embedding.id B,
          fun _ h => (List.not_mem_nil h).elim⟩
      · intro X Test _ _ e
        exact ⟨e⟩
  | cons alpha profiles ih =>
      obtain ⟨W, hW, T, hCanon, hT, hTPart, hTCover⟩ :=
        ih (fun beta hb => hProfiles beta (List.mem_cons_of_mem _ hb))
      letI : Finite W := hW
      obtain ⟨oldInT, _⟩ := hCanon
        (fun _ => Classical.choice (inferInstance : Nonempty Color))
      obtain ⟨aB⟩ := hProfiles alpha (List.mem_cons_self ..)
      let aT : Partite.ProjectedEmbedding A T alpha.toFunctionEmbedding :=
        aB.comp oldInT
      obtain ⟨Y, hY, C, hPicture, hC, hCPart, hCCover⟩ :=
        pictureLemma_protected_unrestricted A D T alpha hA hT hTPart aT Color
      refine ⟨Y, hY, C, ?_, hC, hCPart, ?_⟩
      · intro chi
        obtain ⟨g, hg⟩ := hPicture (fun e => chi e.val)
        obtain ⟨f, hf⟩ := hCanon (fun e => chi (g.toEmbedding.comp e))
        refine ⟨g.comp f, ?_⟩
        intro beta hBeta e1 e2
        simp only [List.map_cons, List.mem_cons] at hBeta
        rcases hBeta with rfl | hBeta
        · exact hg (e1.comp f) (e2.comp f)
        · exact hf beta hBeta e1 e2
      · intro X Test hClosed hIrred e
        obtain ⟨d⟩ := hCCover Test hClosed hIrred e
        exact hTCover Test hClosed hIrred d

/-- Fully CONSTRUCTED closed-test Ramsey witness for any finite
U-closed A,B and any ambient D with the original Ramsey arrow.
No U-closedness of D and no relative-A-copy condition are needed.

The initial picture is the disjoint union of B-copies indexed by
embeddings into D. Every relevant A->D profile factors through such
a B-copy. The complete unrestricted pass from the preceding theorem
produces a finite closed C, and the initial Ramsey colouring extraction
turns CanonicalOn into the GLOBAL Ramsey arrow for B-copies in C.

Each closed irreducible test of C factors through an original B-copy
in the initial picture. The protected part projection targets the
ORIGINAL D, even when D itself is nonclosed. -/
theorem closed_ramsey_unrestricted
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V)
    (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (Color : Type*) [Fintype Color] [Nonempty Color]
    (hArrow : StructuralRamsey.Arrow A B D Color) :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      StructuralRamsey.Arrow A B C.toRelStructure Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B)) := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D Color hArrow
  let S0 := (initialStage B D).system
  have hS0 : IsUClosed rules S0.toRelStructure :=
    Initial.picture_isUClosed B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding) hB
  have hS0Part : IsClosedUHomomorphismEmbedding rules S0.toRelStructure D S0.part :=
    Initial.picture_isClosedPartiteOver B D
      (fun gamma : RelStructure.Embedding B D => gamma)
  let profiles : List (RelStructure.Embedding A D) :=
    (allRelevant A B D).map (fun gamma => gamma.1)
  have hProfiles : ∀ alpha ∈ profiles,
      Nonempty (Partite.ProjectedEmbedding A S0 alpha.toFunctionEmbedding) := by
    intro alpha ha
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp ha
    obtain ⟨beta, e, hfac⟩ := r.2
    have hAlpha : alpha = beta.comp e := by
      calc
        alpha = r.1 := heq.symm
        _ = beta.comp e := hfac
    rw [hAlpha]
    exact ⟨initialProjectedCopy B D beta e⟩
  obtain ⟨Y, hY, C, hCanon, hC, hCPart, hCCover⟩ :=
    unrestricted_protected_pass A D S0 hA hS0 hS0Part
      profiles hProfiles Color
  have hCanon' : CanonicalOn A S0 C
      (projectionProfiles A B D (allRelevant A B D)) Color := by
    simpa only [profiles, projectionProfiles, List.map_map,
      Function.comp_def] using hCanon
  refine ⟨Y, hY, C,
    arrow_of_initial_canonical A B D C Color hArrow hCanon',
    hC, hCPart, ?_⟩
  intro X Test hClosed hIrred emb
  obtain ⟨d⟩ := hCCover Test hClosed hIrred emb
  obtain ⟨i, g, hg⟩ :=
    Initial.closed_test_factor_copy B
      (fun gamma : RelStructure.Embedding B D => gamma.toFunctionEmbedding)
      Test hClosed hIrred d
  exact ⟨g⟩

end StructuralRamsey.Partite.Induced
