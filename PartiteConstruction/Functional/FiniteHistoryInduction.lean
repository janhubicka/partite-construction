import PartiteConstruction.Functional.FiniteHistoryRankBound
import PartiteConstruction.Functional.FreeAmalgamEmbeddedInduction
import PartiteConstruction.Functional.TreeExtensionAutoHistoryGlue

/-! # Finite-rank projected-history induction through a functional amalgam

The existing combined functional-history invariant is indexed by generator
rank n.  A full test of at most n vertices is therefore within the same
rank, even when the ambient side contains many more vertices.

The following induction starts from the two generator-rank-n side
invariants, not from a much stronger whole-side completion at all ranks.
In the mixed case the full pullback gives three smaller tests, whose
recursively constructed projected-history completions are available.
Only their simultaneous extension over a common strict separator tree
must still be supplied.

This is the exact local form needed by one functional EHN Picture attachment.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {U H E F C VB P : Type v}
variable {A : Structure L U} {Douter : Structure L P}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C} {Base : Structure L VB}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- History completions for all full tests with at most n vertices follow
from both pure-side rank-n invariants and one mixed-root synchronization
hypothesis receiving completed common/left/right smaller tests. -/
theorem finiteBoundedHistoryCompletion_of_relativeMixed
    [Fintype P] [Nonempty P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (p : C → P) (n : ℕ)
    (hSideLeft : FunctionalHistoryTreeLike
      (A := A) (D := Douter) (C := Left) (Base := Base)
      (p ∘ iL) n)
    (hSideRight : FunctionalHistoryTreeLike
      (A := A) (D := Douter) (C := Right) (Base := Base)
      (p ∘ iR) n)
    (hMixed :
      ∀ {X : Type v} [Finite X]
        (Src : Structure L X) (e : Embedding Src Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        Nat.card X ≤ n →
        HasProjectedHistoryTreeCompletion Base pb.common
          (p ∘ (e.comp (pb.leftIn.comp pb.toLeft))) →
        HasProjectedHistoryTreeCompletion Base pb.left
          (p ∘ (e.comp pb.leftIn)) →
        HasProjectedHistoryTreeCompletion Base pb.right
          (p ∘ (e.comp pb.rightIn)) →
        ∀ history : List (Set P),
          ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
            TreeAmalgam Base G Start ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toLeft q ((p ∘ e) ∘ pb.leftIn)
              (history ++ singletonProjectedHistory P) ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toRight q ((p ∘ e) ∘ pb.rightIn)
              (history ++ singletonProjectedHistory P)) :
    ∀ {X : Type v} [Finite X]
      (Src : Structure L X) (e : Embedding Src Whole),
      Nat.card X ≤ n →
      HasProjectedHistoryTreeCompletion Base Src (p ∘ e) := by
  classical
  let Q : ∀ {X : Type v},
      (Src : Structure L X) → Embedding Src Whole → Prop :=
    fun {X} Src e =>
      ∀ [Finite X], Nat.card X ≤ n →
        HasProjectedHistoryTreeCompletion Base Src (p ∘ e)

  have hPureL :
      ∀ {X : Type v} [Finite X]
        (Src : Structure L X) (e : Embedding Src Whole),
        (∀ x : X, ∃ a : E, e x = iL a) →
        Q Src e := by
    intro X _ Src e hpure
    intro _ hCard
    let j : Embedding Src Left := e.factorThroughRange iL hpure
    have hproj : (p ∘ iL) ∘ j = p ∘ e := by
      funext x
      change p (iL (j x)) = p (e x)
      exact congrArg p (Classical.choose_spec (hpure x)).symm
    rw [← hproj]
    exact hSideLeft.fullProjectedHistory_of_smallEmbedding Src j hCard

  have hPureR :
      ∀ {X : Type v} [Finite X]
        (Src : Structure L X) (e : Embedding Src Whole),
        (∀ x : X, ∃ b : F, e x = iR b) →
        Q Src e := by
    intro X _ Src e hpure
    intro _ hCard
    let j : Embedding Src Right := e.factorThroughRange iR hpure
    have hproj : (p ∘ iR) ∘ j = p ∘ e := by
      funext x
      change p (iR (j x)) = p (e x)
      exact congrArg p (Classical.choose_spec (hpure x)).symm
    rw [← hproj]
    exact hSideRight.fullProjectedHistory_of_smallEmbedding Src j hCard

  have hMixedQ :
      ∀ {X : Type v} [Finite X]
        (Src : Structure L X) (e : Embedding Src Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        Q pb.common (e.comp (pb.leftIn.comp pb.toLeft)) →
        Q pb.left (e.comp pb.leftIn) →
        Q pb.right (e.comp pb.rightIn) →
        Q Src e := by
    intro X _ Src e pb hNotL hNotR hCommonQ hLeftQ hRightQ
    intro _ hCard
    letI : Fintype X := Fintype.ofFinite X
    letI : Finite pb.Left :=
      Finite.of_injective pb.leftIn pb.leftIn.injective
    letI : Finite pb.Right :=
      Finite.of_injective pb.rightIn pb.rightIn.injective
    letI : Finite pb.Common :=
      Finite.of_injective pb.toLeft pb.toLeft.injective
    letI : Fintype pb.Left := Fintype.ofFinite pb.Left
    letI : Fintype pb.Right := Fintype.ofFinite pb.Right
    letI : Fintype pb.Common := Fintype.ofFinite pb.Common

    have hCardX : Fintype.card X ≤ n := by
      simpa only [Nat.card_eq_fintype_card] using hCard
    have hCardLeft : Nat.card pb.Left ≤ n := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card pb.Left ≤ Fintype.card X :=
          Fintype.card_le_of_injective pb.leftIn pb.leftIn.injective
        _ ≤ n := hCardX
    have hCardRight : Nat.card pb.Right ≤ n := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card pb.Right ≤ Fintype.card X :=
          Fintype.card_le_of_injective pb.rightIn pb.rightIn.injective
        _ ≤ n := hCardX
    have hCardCommon : Nat.card pb.Common ≤ n := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card pb.Common ≤ Fintype.card pb.Left :=
          Fintype.card_le_of_injective pb.toLeft pb.toLeft.injective
        _ ≤ Fintype.card X :=
          Fintype.card_le_of_injective pb.leftIn pb.leftIn.injective
        _ ≤ n := hCardX

    have hCommon :
        HasProjectedHistoryTreeCompletion Base pb.common
          (p ∘ (e.comp (pb.leftIn.comp pb.toLeft))) :=
      hCommonQ hCardCommon
    have hLeft :
        HasProjectedHistoryTreeCompletion Base pb.left
          (p ∘ (e.comp pb.leftIn)) :=
      hLeftQ hCardLeft
    have hRight :
        HasProjectedHistoryTreeCompletion Base pb.right
          (p ∘ (e.comp pb.rightIn)) :=
      hRightQ hCardRight

    change HasProjectedHistoryTreeCompletion Base Src (p ∘ e)
    intro history
    obtain ⟨G, Start, q, hStart, hRelLeft, hRelRight⟩ :=
      hMixed Src e pb hNotL hNotR hCard
        hCommon hLeft hRight history
    obtain ⟨Z, Target, hExt, f, hf, _hcompat, _hroot, hHist⟩ :=
      LocallyClosedTreeCompletable.glueRelative_withAutomaticProjectedHistory
        (Base := Base) pb.free q (p ∘ e) history hRelLeft hRelRight
    exact ⟨Z, Target, hExt.toTree hStart, f, hf, hHist⟩

  have hInd :
      ∀ {X : Type v} [Finite X]
        (Src : Structure L X) (e : Embedding Src Whole),
        Q Src e :=
    finite_embedded_induction hSrc Q hPureL hPureR hMixedQ
  intro X _ Src e hCard
  exact hInd Src e hCard

end StructuralRamsey.Structure.IsFreeAmalgam
