import PartiteConstruction.Partite.InducedPicture
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Iterated.ProjectedPartialMixedGlue
import PartiteConstruction.Iterated.PureCoreProjectedHistory
import PartiteConstruction.Iterated.PureCopyProjectedHistory
import PartiteConstruction.Iterated.ControlCompletionCompatible
import PartiteConstruction.Iterated.TreeCompletion

/-! # One Picture step for local tree completability

Projected partial intersections on the fixed base D carry the coherence needed in the
hard mixed case.  The old Picture stage itself needs only local tree
completability.  This is exactly the invariant occurring in sparsening
property (2): no ambient-A control clause is required in the conclusion.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X : Type v}

theorem canonicalStep_locallyTreeCompletable_projectedPartial
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    [Finite U] [Finite V] [Finite P] [Finite X]
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id (n - 1))
    (hC₀ :
      RelStructure.LocallyTreeCompletable
        B C₀.toRelStructure n)
    (hPartite : C₀.IsPartiteOver D)
    (N : ℕ) (hN : 0 < N) :
    RelStructure.LocallyTreeCompletable B
      (Partite.Picture.build C₀ α.toFunctionEmbedding
        (Partite.Induced.power
          (C₀.restrict α.toFunctionEmbedding) N)).toRelStructure n := by
  classical
  let αf := α.toFunctionEmbedding
  let R := C₀.restrict αf
  have hR : R.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver D C₀ A hPartite α
  let E := Partite.Induced.power R N
  have hE : E.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hR hN
  let Core := E.relabel αf
  have hCorePartite : Core.IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver (A := A) (B := E) hE α
  let C₁ := Partite.Picture.build C₀ αf E
  have hC₁Partite : C₁.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      C₀ (C₀.support αf) Core
      (Partite.Picture.attachingMap C₀ αf E) hPartite hCorePartite

  intro S hScard
  let p : Partite.Picture.Vertex C₀ αf E → P := C₁.part
  let I : Finset P := S.image p
  by_cases hsmall : I.card < n
  · obtain ⟨Y, T, hTree, f, hf, _hPart, _hHist⟩ :=
      RelStructure.ProjectedPartialLocallyTreeLike.witness_of_homEmbedding_image
        hD p hC₁Partite S (by
          change I.card ≤ n - 1
          omega) []
    exact ⟨Y, T, hTree, f, hf⟩
  · have hIle : I.card ≤ n := by
      calc
        I.card ≤ S.card := Finset.card_image_le
        _ ≤ n := hScard
    have hIeq : I.card = n := by omega
    have hScardEq : S.card = n := by
      have hIS : I.card ≤ S.card := Finset.card_image_le
      omega
    have hinjS :
        ∀ x ∈ S, ∀ y ∈ S, p x = p y → x = y := by
      exact Finset.card_image_iff.mp (by
        rw [hIeq, hScardEq])

    let Tset : Set (Partite.Picture.Vertex C₀ αf E) := ↑S
    let Small := C₁.toRelStructure.induce Tset
    let smallIncl : RelStructure.Embedding Small C₁.toRelStructure :=
      RelStructure.inclusion C₁.toRelStructure Tset
    have hpSmall : Small.IsHomomorphismEmbedding D
        (p ∘ Subtype.val) := by
      exact hC₁Partite.comp smallIncl.isHomomorphismEmbedding

    by_cases hcore :
        ∀ z : Tset, ∃ w : Partite.Induced.Vertex R N,
          z.1 = Partite.Picture.coreEmbedding C₀ αf E w
    · obtain ⟨f, hf, _hPart, _hHist⟩ :=
        pureCore_projectedHistoryWitness
          A B D C₀ α E hA eAB hE S hcore []
      exact ⟨V, B, RelStructure.TreeAmalgam.copy (Iso.refl B), f, hf⟩
    · push Not at hcore
      obtain ⟨z₀, hz₀⟩ := hcore
      cases hzval : z₀.1 with
      | inl w =>
          exact (hz₀ w (by
            change z₀.1 = Sum.inl w
            exact hzval)).elim
      | inr pair =>
          let i := pair.1
          let out₀ := pair.2
          let Brel := C₀.toRelStructure
          let Ssupp := C₀.support αf
          let Dcore := Core.toRelStructure

          have hzOutside :
              RelStructure.Attachment.OutsideAt (S := Ssupp) i z₀.1 := by
            refine ⟨out₀, ?_⟩
            exact hzval

          by_cases hcopy :
              ∀ z : Tset,
                RelStructure.Attachment.InCopy
                  Brel Ssupp Dcore
                  (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                  i z.1
          · have hrange :
                ∀ z : Tset, ∃ x : X,
                  smallIncl z =
                    (Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding x := by
              intro z
              rcases hcopy z with ⟨x, hx⟩
              exact ⟨x, hx⟩
            let eCopy : RelStructure.Embedding Small C₀.toRelStructure :=
              smallIncl.factorThroughRange
                (Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding hrange
            have hSmall :
                RelStructure.LocallyTreeCompletable B Small n :=
              hC₀.pullback_embedding eCopy
            letI : Fintype Tset := Fintype.ofFinite Tset
            have hcardT : Fintype.card Tset ≤ n := by
              simpa [Tset] using hScard
            have hWhole := hSmall.fullWitness hcardT
            simpa [Small, Tset] using hWhole
          · push Not at hcopy
            obtain ⟨z₁, hz₁⟩ := hcopy

            let Piece :=
              RelStructure.Attachment.Piece
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let Rest :=
              RelStructure.Attachment.Rest
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let Overlap :=
              RelStructure.Attachment.Overlap
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let PieceV :=
              RelStructure.Attachment.PieceV
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let RestV :=
              RelStructure.Attachment.RestV
                (W := Partite.Induced.Vertex R N)
                (I := Partite.Embedding (C₀.restrict αf) E)
                Ssupp Tset i
            let OverlapV :=
              RelStructure.Attachment.OverlapV
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let sPiece :=
              RelStructure.Attachment.overlapToPiece
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let sRest :=
              RelStructure.Attachment.overlapToRest
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let iPiece :=
              RelStructure.Attachment.pieceInclusion
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            let iRest :=
              RelStructure.Attachment.restInclusion
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i
            have hFree :
                RelStructure.IsFreeAmalgam sPiece sRest iPiece iRest :=
              RelStructure.Attachment.decompose
                Brel Ssupp Dcore
                (fun j => (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                Tset i

            let pSmall : Tset → P := p ∘ Subtype.val
            let pPiece : PieceV → P := pSmall ∘ iPiece
            let pRest : RestV → P := pSmall ∘ iRest

            letI : Fintype Tset := Fintype.ofFinite Tset
            letI : Fintype PieceV := Fintype.ofFinite PieceV
            letI : Fintype RestV := Fintype.ofFinite RestV

            have hPieceSubset :
                ((Finset.univ : Finset PieceV).image pPiece) ⊆
                  I.erase (p z₁.1) := by
              intro q hq
              rcases Finset.mem_image.mp hq with ⟨e, _, rfl⟩
              have hmemI : pPiece e ∈ I := by
                apply Finset.mem_image.mpr
                exact ⟨(iPiece e).1, (iPiece e).2, rfl⟩
              have hne : pPiece e ≠ p z₁.1 := by
                intro heq
                have hv : (iPiece e).1 = z₁.1 :=
                  hinjS (iPiece e).1 (iPiece e).2 z₁.1 z₁.2 heq
                have hpieceZ :
                    RelStructure.Attachment.InCopy
                      Brel Ssupp Dcore
                      (fun j =>
                        (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                      i z₁.1 := by
                  have hePiece := e.property
                  change RelStructure.Attachment.InCopy
                    Brel Ssupp Dcore
                    (fun j =>
                      (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                    i (iPiece e).1 at hePiece
                  rw [hv] at hePiece
                  exact hePiece
                exact hz₁ hpieceZ
              exact Finset.mem_erase.mpr ⟨hne, hmemI⟩
            have hPieceCard :
                ((Finset.univ : Finset PieceV).image pPiece).card ≤ n - 1 := by
              calc
                ((Finset.univ : Finset PieceV).image pPiece).card
                    ≤ (I.erase (p z₁.1)).card :=
                  Finset.card_le_card hPieceSubset
                _ = I.card - 1 := by
                  rw [Finset.card_erase_of_mem]
                  exact Finset.mem_image.mpr ⟨z₁.1, z₁.2, rfl⟩
                _ ≤ n - 1 := by rw [hIeq]

            have hRestSubset :
                ((Finset.univ : Finset RestV).image pRest) ⊆
                  I.erase (p z₀.1) := by
              intro q hq
              rcases Finset.mem_image.mp hq with ⟨e, _, rfl⟩
              have hmemI : pRest e ∈ I := by
                apply Finset.mem_image.mpr
                exact ⟨(iRest e).1, (iRest e).2, rfl⟩
              have hne : pRest e ≠ p z₀.1 := by
                intro heq
                have hv : (iRest e).1 = z₀.1 :=
                  hinjS (iRest e).1 (iRest e).2 z₀.1 z₀.2 heq
                have hrestZ :
                    ¬ RelStructure.Attachment.OutsideAt
                      (S := Ssupp) i z₀.1 := by
                  have heRest := e.property
                  change ¬ RelStructure.Attachment.OutsideAt
                    (S := Ssupp) i (iRest e).1 at heRest
                  rw [hv] at heRest
                  exact heRest
                exact hrestZ hzOutside
              exact Finset.mem_erase.mpr ⟨hne, hmemI⟩
            have hRestCard :
                ((Finset.univ : Finset RestV).image pRest).card ≤ n - 1 := by
              calc
                ((Finset.univ : Finset RestV).image pRest).card
                    ≤ (I.erase (p z₀.1)).card :=
                  Finset.card_le_card hRestSubset
                _ = I.card - 1 := by
                  rw [Finset.card_erase_of_mem]
                  exact Finset.mem_image.mpr ⟨z₀.1, z₀.2, rfl⟩
                _ ≤ n - 1 := by rw [hIeq]

            have hOverlapRange :
                ∀ d : OverlapV,
                  ∃ a : U, pSmall (iPiece (sPiece d)) = α a := by
              intro d
              have hInCopy :
                  RelStructure.Attachment.InCopy
                    Brel Ssupp Dcore
                    (fun j =>
                      (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                    i d.1.1 := d.2.1
              have hNotOut :
                  ¬ RelStructure.Attachment.OutsideAt
                    (S := Ssupp) i d.1.1 := d.2.2
              rcases hInCopy with ⟨x, hx⟩
              have hxSupp : x ∈ Ssupp := by
                by_contra hxS
                apply hNotOut
                refine ⟨⟨x, hxS⟩, ?_⟩
                rw [hx]
                exact RelStructure.Attachment.copyMap_not_mem i x hxS
              rcases hxSupp with ⟨a, ha⟩
              refine ⟨a, ?_⟩
              change C₁.part d.1.1 = α a
              rw [hx]
              calc
                C₁.part
                    (RelStructure.Attachment.copyMap
                      Brel Ssupp Dcore
                      (fun j =>
                        (Partite.Picture.attachingMap C₀ αf E j).toEmbedding)
                      i x) =
                    C₀.part x :=
                  Partite.Attachment.part_copyMap
                    C₀ Ssupp Core
                    (Partite.Picture.attachingMap C₀ αf E) i x
                _ = αf a := ha.symm
                _ = α a := rfl

            obtain ⟨Y, T, hTree, f, hf, _hctrl⟩ :=
              RelStructure.LocallyTreeLike.glueProjectedFull_projectedPartial
                hA eAB hFree pSmall hpSmall α hOverlapRange
                (n - 1) hD hPieceCard hRestCard
            have hf' :
                (C₁.toRelStructure.induce (↑S : Set _)).IsHomomorphismEmbedding T f := by
              simpa [RelStructure.Attachment.Small, Tset, Brel, Ssupp,
                Dcore, C₁, Core, E, R, αf, Partite.Picture.build,
                Partite.Attachment.attach] using hf
            exact ⟨Y, T, hTree, f, hf'⟩

end StructuralRamsey.Partite.Iterated
