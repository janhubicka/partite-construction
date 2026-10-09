import PartiteConstruction.Ramsey.ClosureProtectedPictureLemma
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness
import PartiteConstruction.Ramsey.ClosureRankOneBase
import PartiteConstruction.Partite.InducedConstruction

/-! # Whole finite passes for the closed-substructure repair

Iterate the ACTUAL protected local Picture lemma over an arbitrary finite
list of A-embeddings into the closed part structure D. Backwards colour
extraction gives CanonicalOn for every listed profile simultaneously.
All closed irreducible tests in the final picture embed in the ORIGINAL
input picture. Thus corrected test membership, and consequently the full
closed rank-one completion invariant, survive a complete pass.

This constructs a finite witness, rather than assuming a protected
refinement operation. The input picture and part structure D are closed;
this is not yet the initial repair over an arbitrary nonclosed C0, and
it does not assert preservation or increment of higher-rank completions.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V P : Type v}

/-- Process every requested part profile while retaining closedness,
protected projection and coverage by the ORIGINAL input picture. -/
theorem protected_pass
    {rules : ClosureDescription L}
    (A : RelStructure L U) (D : RelStructure L P)
    (B : System L P V)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite U] [Finite V]
    (profiles : List (RelStructure.Embedding A D))
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      CanonicalOn A B C (profiles.map (fun a => a.toFunctionEmbedding)) κ ∧
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
      · intro χ
        exact ⟨Partite.Embedding.id B,
          fun _ h => (List.not_mem_nil h).elim⟩
      · intro X Test _ _ e
        exact ⟨e⟩
  | cons alpha profiles ih =>
      obtain ⟨W, hW, T, hCanon, hT, hTPart, hTCover⟩ := ih
      letI : Finite W := hW
      obtain ⟨oldInT, _⟩ := hCanon
        (fun _ => Classical.choice (inferInstance : Nonempty κ))
      let aT : RelStructure.Embedding A T.toRelStructure :=
        oldInT.toEmbedding.comp aB
      obtain ⟨Y, hY, C, hPicture, hC, hCPart, hCCover⟩ :=
        pictureLemma_protected A D T alpha hA hD hT hTPart aT κ
      refine ⟨Y, hY, C, ?_, hC, hCPart, ?_⟩
      · intro χ
        obtain ⟨g, hg⟩ := hPicture (fun e => χ e.val)
        obtain ⟨f, hf⟩ := hCanon (fun e => χ (g.toEmbedding.comp e))
        refine ⟨g.comp f, ?_⟩
        intro beta hBeta e1 e2
        simp only [List.map_cons, List.mem_cons] at hBeta
        rcases hBeta with rfl | hBeta
        · exact hg (e1.comp f) (e2.comp f)
        · exact hf beta hBeta e1 e2
      · intro X Test hClosed hIrred e
        obtain ⟨d⟩ := hCCover Test hClosed hIrred e
        exact hTCover Test hClosed hIrred d

/-- Corrected (4b) and all closed rank-at-most-one completions are
retained through the whole finite pass. Rank zero and empty tests are
included. This is the BASE invariant, not the j-to-j+1 theorem. -/
theorem protected_pass_with_rank_one
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    (A : RelStructure L U) (D : RelStructure L P)
    (B : System L P V)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (hTests : ClosedUIrreduciblesIn K rules B.toRelStructure)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite U] [Finite V]
    (profiles : List (RelStructure.Embedding A D))
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (C : System L P W),
      CanonicalOn A B C (profiles.map (fun a => a.toFunctionEmbedding)) κ ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      ClosedUIrreduciblesIn K rules C.toRelStructure ∧
      (∀ (S : Set W) [Fintype S],
        IsUClosed rules (C.toRelStructure.induce S) →
        USize rules (C.toRelStructure.induce S) ≤ 1 →
        HasClosedUKCompletion K rules (C.toRelStructure.induce S)) := by
  obtain ⟨W, hW, C, hCanon, hC, hCPart, hCover⟩ :=
    protected_pass A D B hA hD hB hPart aB profiles κ
  have hCTests : ClosedUIrreduciblesIn K rules C.toRelStructure := by
    intro X Test hClosed hIrred e
    obtain ⟨d⟩ := hCover Test hClosed hIrred e
    exact hTests Test hClosed hIrred d
  refine ⟨W, hW, C, hCanon, hC, hCPart, hCTests, ?_⟩
  intro S hS hClosed hRank
  have hKS : K (C.toRelStructure.induce S) :=
    hCTests (C.toRelStructure.induce S) hClosed
      (hClosed.uIrreducible_of_USize_le_one hRank)
      (inclusion C.toRelStructure S)
  let e := RelStructure.Embedding.id (C.toRelStructure.induce S)
  exact ⟨S, inferInstance, C.toRelStructure.induce S, hKS,
    hKIrr _ hKS, e, e.isClosedUHomomorphismEmbedding rules⟩

end StructuralRamsey.Partite.Induced
