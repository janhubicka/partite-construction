import PartiteConstruction.Ramsey.ClosureProtectedPass

/-! # Protected Picture construction over nonclosed controls

Only the actual attaching support needs to be relatively closed in the
old closed picture. No closedness of the control D is used in gluing.
For iteration, relative closedness of each chosen A-copy in D supplies
this support condition by preimage under the positive old projection.
The actual native all-embeddings Picture and finite Hales--Jewett core
are retained. No semi-closed input is declared closed by convention.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P Q V W : Type v}

/-- The actual Picture gluing step needs a closed support, not a closed
control. Closedness, protected projection and old-copy coverage hold. -/
theorem picture_build_protected_of_closed_support
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (E : System L Q W)
    (hB : IsUClosed rules B.toRelStructure)
    (hE : IsUClosed rules E.toRelStructure)
    (hSupport : IsUSubstructure rules B.toRelStructure
      (B.support alpha.toFunctionEmbedding))
    (hBPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (hEPart : IsClosedUHomomorphismEmbedding rules E.toRelStructure A E.part)
    (aB : RelStructure.Embedding A B.toRelStructure) :
    IsUClosed rules (Picture.build B alpha.toFunctionEmbedding E).toRelStructure ∧
    IsClosedUHomomorphismEmbedding rules
      (Picture.build B alpha.toFunctionEmbedding E).toRelStructure
      D (Picture.build B alpha.toFunctionEmbedding E).part ∧
    (∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      RelStructure.Embedding Test
        (Picture.build B alpha.toFunctionEmbedding E).toRelStructure →
      Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  let af := alpha.toFunctionEmbedding
  let S := B.support af
  let maps : Partite.Embedding (B.restrict af) E →
      RelStructure.Embedding (B.toRelStructure.induce S)
        (E.relabel af).toRelStructure :=
    fun i => (Picture.attachingMap B af E i).toEmbedding
  have hWhole := RelStructure.Attachment.attach_isUClosed
    B.toRelStructure S (E.relabel af).toRelStructure maps hB hE hSupport
  refine ⟨hWhole, ?_, ?_⟩
  · let pCore : W → P := fun x => alpha (E.part x)
    let pCopy : Partite.Embedding (B.restrict af) E → V → P := fun _ x => B.part x
    have hCore : IsClosedUHomomorphismEmbedding rules
        (E.relabel af).toRelStructure D pCore :=
      (alpha.isClosedUHomomorphismEmbedding rules).comp hEPart
    have hCompat : ∀ i (x : S), pCore (maps i x) = pCopy i x.1 := by
      intro i x
      exact (Picture.attachingMap B af E i).map_part x
    have hFold := RelStructure.Attachment.fold_isClosedUHomomorphismEmbedding
      B.toRelStructure S (E.relabel af).toRelStructure maps
      hB hSupport hWhole D pCore pCopy hCore (fun _ => hBPart) hCompat
    have hEq : RelStructure.Attachment.fold pCore pCopy =
        (Picture.build B af E).part := by
      funext z
      cases z <;> rfl
    rw [← hEq]
    exact hFold
  · intro Z Test hClosed hIrred e
    rcases RelStructure.Attachment.closed_test_core_or_copy
        B.toRelStructure S (E.relabel af).toRelStructure maps
        hB hSupport hWhole Test hClosed hIrred e with ⟨g, hg⟩ | ⟨i, g, hg⟩
    · obtain ⟨d, hd⟩ := hEPart.on_test Test hClosed hIrred g
      exact ⟨aB.comp d⟩
    · exact ⟨g⟩

/-- A finite protected local Ramsey witness over arbitrary D, with
relative closedness of the actual support supplied explicitly. -/
theorem pictureLemma_protected_of_closed_support
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B.toRelStructure)
    (hSupport : IsUSubstructure rules B.toRelStructure
      (B.support alpha.toFunctionEmbedding))
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite Q] [Finite V] (Color : Type*) [Fintype Color] :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      PictureProperty A B alpha.toFunctionEmbedding C Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  classical
  let R := B.restrict alpha.toFunctionEmbedding
  have hRClosed : IsUClosed rules R.toRelStructure :=
    hB.induce_of_USubstructure (B.support alpha.toFunctionEmbedding) hSupport
  have hRPart := restrict_isClosedPartiteOver A D B alpha hPart
  have hROrd : R.IsPartiteOver A :=
    StructuralRamsey.RelStructure.IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hRPart hRClosed
  obtain ⟨N, hN, hArrow⟩ := partiteLemma (A := A) (B := R) hROrd Color
  let E := power R N
  have hEClosed := power_isUClosed R hROrd hA hRClosed hN
  have hEPart := power_part_protected R hRClosed hRPart hN
  obtain ⟨hClosed, hProjection, hCoverage⟩ :=
    picture_build_protected_of_closed_support A D B alpha E
      hB hEClosed hSupport hPart hEPart aB
  exact ⟨Picture.Vertex B alpha.toFunctionEmbedding E, inferInstance,
    Picture.build B alpha.toFunctionEmbedding E,
    Picture.property B alpha.toFunctionEmbedding E Color hArrow,
    hClosed, hProjection, hCoverage⟩

/-- Whole finite pass when the chosen A-profiles are relative
U-substructures of the control. The control need not be closed. -/
theorem protected_pass_of_relative_profiles
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P) (B : System L P V)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (aB : RelStructure.Embedding A B.toRelStructure)
    [Finite Q] [Finite V]
    (profiles : List (RelStructure.Embedding A D))
    (hProfiles : ∀ alpha ∈ profiles, IsUSubstructure rules D (Set.range alpha))
    (Color : Type*) [Fintype Color] [Nonempty Color] :
    ∃ (Y : Type v) (_ : Finite Y) (C : System L P Y),
      CanonicalOn A B C (profiles.map (fun a => a.toFunctionEmbedding)) Color ∧
      IsUClosed rules C.toRelStructure ∧
      IsClosedUHomomorphismEmbedding rules C.toRelStructure D C.part ∧
      (∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        RelStructure.Embedding Test C.toRelStructure →
        Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  classical
  induction profiles with
  | nil =>
      refine ⟨V, inferInstance, B, ?_, hB, hPart, ?_⟩
      · intro chi
        exact ⟨Partite.Embedding.id B, fun _ h => (List.not_mem_nil h).elim⟩
      · intro Z Test _ _ e
        exact ⟨e⟩
  | cons alpha profiles ih =>
      obtain ⟨Y, hY, T, hCanon, hT, hTPart, hTCover⟩ :=
        ih (fun a ha => hProfiles a (List.mem_cons_of_mem _ ha))
      letI : Finite Y := hY
      obtain ⟨oldInT, hOld⟩ := hCanon
        (fun _ => Classical.choice (inferInstance : Nonempty Color))
      let aT := oldInT.toEmbedding.comp aB
      have hSupport : IsUSubstructure rules T.toRelStructure
          (T.support alpha.toFunctionEmbedding) :=
        (hProfiles alpha (List.mem_cons_self ..)).preimage_homomorphism hTPart.1
      obtain ⟨Z, hZ, C, hPicture, hC, hCPart, hCCover⟩ :=
        pictureLemma_protected_of_closed_support A D T alpha
          hA hT hSupport hTPart aT Color
      refine ⟨Z, hZ, C, ?_, hC, hCPart, ?_⟩
      · intro chi
        obtain ⟨g, hg⟩ := hPicture (fun e => chi e.val)
        obtain ⟨f, hf⟩ := hCanon (fun e => chi (g.toEmbedding.comp e))
        refine ⟨g.comp f, ?_⟩
        intro beta hBeta e1 e2
        simp only [List.map_cons, List.mem_cons] at hBeta
        rcases hBeta with rfl | hBeta
        · exact hg (e1.comp f) (e2.comp f)
        · exact hf beta hBeta e1 e2
      · intro Z Test hClosed hIrred e
        obtain ⟨d⟩ := hCCover Test hClosed hIrred e
        exact hTCover Test hClosed hIrred d

end StructuralRamsey.Partite.Induced
