import PartiteConstruction.Functional.HistoryRootedWitness
import PartiteConstruction.Functional.FreeAmalgamPullback
import PartiteConstruction.Functional.FullFreeAmalgam

/-! # Functional history gluing over a whole irreducible root

This is the function-language counterpart of the relational root-budget
argument.  A closed finite test in a free amalgam is pulled back to its two
closed sides.  On each side we test those vertices together with the *whole*
ambient irreducible root.  Recording that root as one source-history set gives
the exact root-isolation needed for full set-valued-function gluing.

The price is a generator budget of `|Root|` on each side.
-/

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {U P VB H E F C : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}
variable {pL : E → P}
variable {pR : F → P}

/-- Free amalgamation over a whole irreducible root preserves closed local
functional tree-completability, provided both ambient sides carry the
generator-budget history invariant. -/
theorem freeAmalgam_irreducibleRoot
    [Finite H] [Finite E] [Finite F]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : Root.Irreducible)
    (n : ℕ)
    (hLeft :
      FunctionalHistoryTreeLike
        (A := A) (D := D) (C := Left) (Base := Base)
        pL (n + Nat.card H))
    (hRight :
      FunctionalHistoryTreeLike
        (A := A) (D := D) (C := Right) (Base := Base)
        pR (n + Nat.card H)) :
    LocallyClosedTreeCompletable Base Whole n := by
  classical
  intro S hScard hS
  let Sset : Set C := ↑S
  let Small : Structure L Sset := Whole.induce Sset hS
  let incSmall : Embedding Small Whole :=
    inclusion Whole Sset hS
  let pb := hSrc.embeddingPullback incSmall

  letI : Finite pb.Left :=
    Finite.of_injective pb.leftIn pb.leftIn.injective
  letI : Finite pb.Right :=
    Finite.of_injective pb.rightIn pb.rightIn.injective
  letI : Finite pb.Common :=
    Finite.of_injective pb.toLeft pb.toLeft.injective
  letI : Fintype pb.Left := Fintype.ofFinite pb.Left
  letI : Fintype pb.Right := Fintype.ofFinite pb.Right
  letI : Fintype Sset := Fintype.ofFinite Sset

  have hLeftCard : Nat.card pb.Left ≤ n := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card pb.Left ≤ Fintype.card Sset :=
        Fintype.card_le_of_injective pb.leftIn pb.leftIn.injective
      _ = S.card := by simp [Sset]
      _ ≤ n := hScard

  have hRightCard : Nat.card pb.Right ≤ n := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card pb.Right ≤ Fintype.card Sset :=
        Fintype.card_le_of_injective pb.rightIn pb.rightIn.injective
      _ = S.card := by simp [Sset]
      _ ≤ n := hScard

  obtain ⟨YL, TL, hTreeL, fL, hfL, tL, hcompatL, hrootL⟩ :=
    FunctionalHistoryTreeLike.rootedWitness
      (A := A) (D := D) (Base := Base)
      hRoot sL pb.leftMap pb.toLeft pb.commonMap
      pb.common_left pb.left_reflect n hLeftCard hLeft

  obtain ⟨YR, TR, hTreeR, fR, hfR, tR, hcompatR, hrootR⟩ :=
    FunctionalHistoryTreeLike.rootedWitness
      (A := A) (D := D) (Base := Base)
      hRoot sR pb.rightMap pb.toRight pb.commonMap
      pb.common_right pb.right_reflect n hRightCard hRight

  let Target := FreeAmalgam.amalgam Root TL TR tL tR
  let jL := FreeAmalgam.leftEmbedding Root TL TR tL tR
  let jR := FreeAmalgam.rightEmbedding Root TL TR tL tR
  have hTgt : IsFreeAmalgam tL tR jL jR :=
    FreeAmalgam.isFreeAmalgam Root TL TR tL tR

  have hcL : tL.ContainedInIrreducible := by
    refine ⟨H, Root, hRoot, tL, ?_⟩
    intro d
    exact ⟨d, rfl⟩
  have hcR : tR.ContainedInIrreducible := by
    refine ⟨H, Root, hRoot, tR, ?_⟩
    intro d
    exact ⟨d, rfl⟩

  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Root TL TR tL tR) Target :=
    FreeAmalgam.treeAmalgam Root TL TR tL tR Base
      hTreeL hTreeR hcL hcR

  let fSmall : Sset → FreeAmalgam.Vertex Root TL TR tL tR :=
    IsFreeAmalgam.functionalLiftMap
      pb.free hTgt pb.commonMap fL fR hcompatL hcompatR

  have hfSmall :
      Small.IsHomomorphismEmbedding Target fSmall :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      pb.free hTgt pb.commonMap fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR

  exact ⟨_, Target, hTree, fSmall, hfSmall⟩

end StructuralRamsey.Structure.LocallyClosedTreeCompletable
