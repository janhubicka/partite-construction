import PartiteConstruction.Partite.InducedPicture
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Iterated.ProjectedGlue
import PartiteConstruction.Iterated.ControlCompletion

/-! # Projected attachments preserve local tree-likeness

This isolates the single geometric step in the weak vertex-size induction.
Only a projected relation/function-graph free attachment is needed: when
the common support projects into a selected A-copy, one attachment preserves
the local rank n.  It applies to the graph of a genuine functional EHN
attachment without replacing its actual Hales--Jewett/partite construction.
-/

namespace StructuralRamsey.RelStructure.Attachment

open StructuralRamsey.RelStructure

noncomputable section

universe u v
variable {L : RelLanguage.{u}} {U V P X Y IX : Type v}

/-- Any projected free attachment preserves weak local tree-likeness:
a small test either lies in the core, lies in one copy, or has two
strictly smaller projected sides glued along a supported A-boundary. -/
theorem locallyTreeLike_of_projected_support
    (A : RelStructure L U) (B : RelStructure L V)
    (D : RelStructure L P)
    (Old : RelStructure L X) (Core : RelStructure L Y)
    (Supp : Set X)
    (maps : IX → RelStructure.Embedding (Old.induce Supp) Core)
    [Finite U] [Finite V] [Finite P] [Finite X] [Finite Y]
    [Finite IX]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hOld : RelStructure.LocallyTreeLike A B Old n)
    (hCore : RelStructure.LocallyTreeLike A B Core n)
    (p : RelStructure.Attachment.Vertex Supp (W := Y) (I := IX) → P)
    (hProj :
      (RelStructure.Attachment.attach Old Supp Core maps).IsHomomorphismEmbedding
        D p)
    (α : RelStructure.Embedding A D)
    (hSupport : ∀ (i : IX) (x : X), x ∈ Supp →
      ∃ a : U,
        p (RelStructure.Attachment.copyMap Old Supp Core maps i x) = α a) :
    RelStructure.LocallyTreeLike A B
      (RelStructure.Attachment.attach Old Supp Core maps) n := by
  classical
  let Whole := RelStructure.Attachment.attach Old Supp Core maps
  intro S hScard
  let IP : Finset P := S.image p
  by_cases hsmall : IP.card < n
  · exact RelStructure.LocallyTreeLike.witness_of_homEmbedding_image
      hA.irreducible hD p hProj S (by
        change IP.card ≤ n - 1
        omega)
  · have hIle : IP.card ≤ n := by
      calc
        IP.card ≤ S.card := Finset.card_image_le
        _ ≤ n := hScard
    have hIeq : IP.card = n := by omega
    have hScardEq : S.card = n := by
      have hIS : IP.card ≤ S.card := Finset.card_image_le
      omega
    have hinjS :
        ∀ x ∈ S, ∀ y ∈ S, p x = p y → x = y := by
      exact Finset.card_image_iff.mp (by
        rw [hIeq, hScardEq])

    let Tset : Set (RelStructure.Attachment.Vertex Supp (W := Y) (I := IX)) := ↑S
    let Small := Whole.induce Tset
    let smallIncl : RelStructure.Embedding Small Whole :=
      RelStructure.inclusion Whole Tset
    have hpSmall : Small.IsHomomorphismEmbedding D
        (p ∘ Subtype.val) := by
      exact hProj.comp smallIncl.isHomomorphismEmbedding

    by_cases hcore :
        ∀ z : Tset, ∃ w : Y,
          z.1 = RelStructure.Attachment.coreEmbedding Old Supp Core maps w
    · let eCore : RelStructure.Embedding Small Core :=
        smallIncl.factorThroughRange
          (RelStructure.Attachment.coreEmbedding Old Supp Core maps) hcore
      have hSmallLTL :
          RelStructure.LocallyTreeLike A B Small n :=
        hCore.pullback_embedding eCore
      letI : Fintype Tset := Fintype.ofFinite Tset
      have hcardT : Fintype.card Tset ≤ n := by
        simpa [Tset] using hScard
      obtain ⟨Y, T, hTree, f, hf, _⟩ :=
        hSmallLTL.fullWitness hcardT
      have hf' :
          (Whole.induce (↑S : Set _)).IsHomomorphismEmbedding T f := by
        simpa [Small, Tset] using hf
      exact RelStructure.LocallyTreeLike.completeControl
        (A := A) (B := B) (C := Whole)
        hA eAB S hTree f hf'
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
          let Brel := Old
          let Ssupp := Supp
          let Dcore := Core

          have hzOutside :
              RelStructure.Attachment.OutsideAt (S := Ssupp) i z₀.1 := by
            refine ⟨out₀, ?_⟩
            exact hzval

          by_cases hcopy :
              ∀ z : Tset,
                RelStructure.Attachment.InCopy
                  Brel Ssupp Dcore
                  maps
                  i z.1
          · have hrange :
                ∀ z : Tset, ∃ x : X,
                  smallIncl z =
                    (RelStructure.Attachment.copyEmbedding Old Supp Core maps i) x := by
              intro z
              rcases hcopy z with ⟨x, hx⟩
              exact ⟨x, hx⟩
            let eCopy : RelStructure.Embedding Small Old :=
              smallIncl.factorThroughRange
                (RelStructure.Attachment.copyEmbedding Old Supp Core maps i) hrange
            have hSmallLTL :
                RelStructure.LocallyTreeLike A B Small n :=
              hOld.pullback_embedding eCopy
            letI : Fintype Tset := Fintype.ofFinite Tset
            have hcardT : Fintype.card Tset ≤ n := by
              simpa [Tset] using hScard
            obtain ⟨Y, T, hTree, f, hf, _⟩ :=
              hSmallLTL.fullWitness hcardT
            have hf' :
                (Whole.induce (↑S : Set _)).IsHomomorphismEmbedding T f := by
              simpa [Small, Tset] using hf
            exact RelStructure.LocallyTreeLike.completeControl
              (A := A) (B := B) (C := Whole)
              hA eAB S hTree f hf'
          · push Not at hcopy
            obtain ⟨z₁, hz₁⟩ := hcopy

            let Piece :=
              RelStructure.Attachment.Piece
                Brel Ssupp Dcore
                maps
                Tset i
            let Rest :=
              RelStructure.Attachment.Rest
                Brel Ssupp Dcore
                maps
                Tset i
            let Overlap :=
              RelStructure.Attachment.Overlap
                Brel Ssupp Dcore
                maps
                Tset i
            let PieceV :=
              RelStructure.Attachment.PieceV
                Brel Ssupp Dcore
                maps
                Tset i
            let RestV :=
              RelStructure.Attachment.RestV
                (W := Y)
                (I := IX)
                Ssupp Tset i
            let OverlapV :=
              RelStructure.Attachment.OverlapV
                Brel Ssupp Dcore
                maps
                Tset i
            let sPiece :=
              RelStructure.Attachment.overlapToPiece
                Brel Ssupp Dcore
                maps
                Tset i
            let sRest :=
              RelStructure.Attachment.overlapToRest
                Brel Ssupp Dcore
                maps
                Tset i
            let iPiece :=
              RelStructure.Attachment.pieceInclusion
                Brel Ssupp Dcore
                maps
                Tset i
            let iRest :=
              RelStructure.Attachment.restInclusion
                Brel Ssupp Dcore
                maps
                Tset i
            have hFree :
                RelStructure.IsFreeAmalgam sPiece sRest iPiece iRest :=
              RelStructure.Attachment.decompose
                Brel Ssupp Dcore
                maps
                Tset i

            let pSmall : Tset → P := p ∘ Subtype.val
            let pPiece : PieceV → P := pSmall ∘ iPiece
            let pRest : RestV → P := pSmall ∘ iRest

            letI : Fintype Tset := Fintype.ofFinite Tset
            letI : Fintype PieceV := Fintype.ofFinite PieceV
            letI : Fintype RestV := Fintype.ofFinite RestV

            have hPieceSubset :
                ((Finset.univ : Finset PieceV).image pPiece) ⊆
                  IP.erase (p z₁.1) := by
              intro q hq
              rcases Finset.mem_image.mp hq with ⟨e, _, rfl⟩
              have hmemI : pPiece e ∈ IP := by
                apply Finset.mem_image.mpr
                exact ⟨(iPiece e).1, (iPiece e).2, rfl⟩
              have hne : pPiece e ≠ p z₁.1 := by
                intro heq
                have hv : (iPiece e).1 = z₁.1 :=
                  hinjS (iPiece e).1 (iPiece e).2 z₁.1 z₁.2 heq
                have hpieceZ :
                    RelStructure.Attachment.InCopy
                      Brel Ssupp Dcore
                      maps
                      i z₁.1 := by
                  have hePiece := e.property
                  change RelStructure.Attachment.InCopy
                    Brel Ssupp Dcore
                    maps
                    i (iPiece e).1 at hePiece
                  rw [hv] at hePiece
                  exact hePiece
                exact hz₁ hpieceZ
              exact Finset.mem_erase.mpr ⟨hne, hmemI⟩
            have hPieceCard :
                ((Finset.univ : Finset PieceV).image pPiece).card ≤ n - 1 := by
              calc
                ((Finset.univ : Finset PieceV).image pPiece).card
                    ≤ (IP.erase (p z₁.1)).card :=
                  Finset.card_le_card hPieceSubset
                _ = IP.card - 1 := by
                  rw [Finset.card_erase_of_mem]
                  exact Finset.mem_image.mpr ⟨z₁.1, z₁.2, rfl⟩
                _ ≤ n - 1 := by rw [hIeq]

            have hRestSubset :
                ((Finset.univ : Finset RestV).image pRest) ⊆
                  IP.erase (p z₀.1) := by
              intro q hq
              rcases Finset.mem_image.mp hq with ⟨e, _, rfl⟩
              have hmemI : pRest e ∈ IP := by
                apply Finset.mem_image.mpr
                exact ⟨(iRest e).1, (iRest e).2, rfl⟩
              have hne : pRest e ≠ p z₀.1 := by
                intro heq
                have hv : (iRest e).1 = z₀.1 :=
                  hinjS (iRest e).1 (iRest e).2 z₀.1 z₀.2 heq
                have hrestZ :
                    ¬ RelStructure.Attachment.OutsideAt (S := Ssupp) i z₀.1 := by
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
                    ≤ (IP.erase (p z₀.1)).card :=
                  Finset.card_le_card hRestSubset
                _ = IP.card - 1 := by
                  rw [Finset.card_erase_of_mem]
                  exact Finset.mem_image.mpr ⟨z₀.1, z₀.2, rfl⟩
                _ ≤ n - 1 := by rw [hIeq]

            have hOverlapRange :
                ∀ d : OverlapV,
                  ∃ a : U, pSmall (iPiece (sPiece d)) = α a := by
              intro d
              have hInCopy :
                  RelStructure.Attachment.InCopy
                    Brel Ssupp Dcore maps i d.1.1 := d.2.1
              have hNotOut :
                  ¬ RelStructure.Attachment.OutsideAt
                    (S := Ssupp) i d.1.1 := d.2.2
              rcases hInCopy with ⟨x, hx⟩
              have hxSupp : x ∈ Supp := by
                by_contra hxS
                apply hNotOut
                refine ⟨⟨x, hxS⟩, ?_⟩
                rw [hx]
                exact RelStructure.Attachment.copyMap_not_mem i x hxS
              obtain ⟨a, ha⟩ := hSupport i x hxSupp
              refine ⟨a, ?_⟩
              change p d.1.1 = α a
              rw [hx]
              exact ha

            obtain ⟨Y, T, hTree, f, hf, _⟩ :=
              RelStructure.LocallyTreeLike.glueProjectedFull
                hA hFree pSmall hpSmall α hOverlapRange
                (n - 1) hD hPieceCard hRestCard
            have hf' :
                (Whole.induce (↑S : Set _)).IsHomomorphismEmbedding T f := by
              simpa [RelStructure.Attachment.Small, Small, Whole,
                Brel, Ssupp, Dcore] using hf
            exact RelStructure.LocallyTreeLike.completeControl
              (A := A) (B := B) (C := Whole)
              hA eAB S hTree f hf'

end

end StructuralRamsey.RelStructure.Attachment
