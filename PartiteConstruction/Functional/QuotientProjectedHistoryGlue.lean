import PartiteConstruction.Functional.HistoryTreeCompletion
import PartiteConstruction.Functional.QuotientBoundaryDiary

/-! # Projected histories through noninjective functional quotient gluing

A noninjective quotient root cannot preserve arbitrary source-side diary sets:
two distinct source-root points may deliberately be identified.  Projected
histories are different.  If the outer projection of the source root factors
through the quotient label map, then identified root points have the same
projected value.  Hence all finite histories of projected subsets survive.

This is the correct history interface for reducible functional separators.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {H E F C₀ G ZL ZR P : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C₀}
variable {Gov : Structure L G}
variable {TL : Structure L ZL} {TR : Structure L ZR}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}
variable {tL : Embedding Gov TL} {tR : Embedding Gov TR}

namespace IsFreeAmalgam

/-- Compatible functional lifting over an arbitrary quotient root preserves
every projected history whose projection factors through that quotient on the
common source root. -/
theorem functionalLiftMap_respectsProjectedSets
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {Target : Type v} {TargetS : Structure L Target}
    {jL : Embedding TL TargetS} {jR : Embedding TR TargetS}
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (hrootR : RootIsolated sR tR q fR)
    (pWhole : C₀ → P) (pL : E → P) (pR : F → P) (pG : G → P)
    (hpL : ∀ x, pWhole (iL x) = pL x)
    (hpR : ∀ x, pWhole (iR x) = pR x)
    (hrootProjL : ∀ d, pL (sL d) = pG (q d))
    (hrootProjR : ∀ d, pR (sR d) = pG (q d))
    (history : List (Set P))
    (hHistL :
      ∀ K ∈ history, ∀ x y : E,
        fL x = fL y → (pL x ∈ K ↔ pL y ∈ K))
    (hHistR :
      ∀ K ∈ history, ∀ x y : F,
        fR x = fR y → (pR x ∈ K ↔ pR y ∈ K)) :
    let lift :=
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
    ∀ K ∈ history, ∀ x y : C₀,
      lift x = lift y →
        (pWhole x ∈ K ↔ pWhole y ∈ K) := by
  classical
  dsimp only
  let lift :=
    functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
  intro K hK x y hxy
  rcases hSrc.covers x with ⟨a, hxa⟩ | ⟨b, hxb⟩
  · rcases hSrc.covers y with ⟨a', hya⟩ | ⟨b, hyb⟩
    · have haa : fL a = fL a' := by
        apply jL.injective
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift x := congrArg lift hxa.symm
          _ = lift y := hxy
          _ = lift (iL a') := congrArg lift hya
          _ = jL (fL a') :=
            functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a'
      have hh := hHistL K hK a a' haa
      simpa [hxa, hya, hpL] using hh
    · have hcross : jL (fL a) = jR (fR b) := by
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift x := congrArg lift hxa.symm
          _ = lift y := hxy
          _ = lift (iR b) := congrArg lift hyb
          _ = jR (fR b) :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b
      obtain ⟨g, hLg, hRg⟩ :=
        (hTgt.overlap (fL a) (fR b)).mp hcross
      obtain ⟨dL, ha, hqdL⟩ := hrootL a g hLg
      obtain ⟨dR, hb, hqdR⟩ := hrootR b g hRg
      have hpEq : pWhole x = pWhole y := by
        calc
          pWhole x = pWhole (iL a) := congrArg pWhole hxa
          _ = pL a := hpL a
          _ = pL (sL dL) := congrArg pL ha
          _ = pG (q dL) := hrootProjL dL
          _ = pG g := congrArg pG hqdL
          _ = pG (q dR) := congrArg pG hqdR.symm
          _ = pR (sR dR) := (hrootProjR dR).symm
          _ = pR b := congrArg pR hb.symm
          _ = pWhole (iR b) := (hpR b).symm
          _ = pWhole y := congrArg pWhole hyb.symm
      rw [hpEq]
  · rcases hSrc.covers y with ⟨a, hya⟩ | ⟨b', hyb⟩
    · have hcross : jL (fL a) = jR (fR b) := by
        calc
          jL (fL a) = lift (iL a) :=
            (functionalLiftMap_left hSrc hTgt q fL fR
              hcompatL hcompatR a).symm
          _ = lift y := congrArg lift hya.symm
          _ = lift x := hxy.symm
          _ = lift (iR b) := congrArg lift hxb
          _ = jR (fR b) :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b
      obtain ⟨g, hLg, hRg⟩ :=
        (hTgt.overlap (fL a) (fR b)).mp hcross
      obtain ⟨dL, ha, hqdL⟩ := hrootL a g hLg
      obtain ⟨dR, hb, hqdR⟩ := hrootR b g hRg
      have hpEq : pWhole y = pWhole x := by
        calc
          pWhole y = pWhole (iL a) := congrArg pWhole hya
          _ = pL a := hpL a
          _ = pL (sL dL) := congrArg pL ha
          _ = pG (q dL) := hrootProjL dL
          _ = pG g := congrArg pG hqdL
          _ = pG (q dR) := congrArg pG hqdR.symm
          _ = pR (sR dR) := (hrootProjR dR).symm
          _ = pR b := congrArg pR hb.symm
          _ = pWhole (iR b) := (hpR b).symm
          _ = pWhole x := congrArg pWhole hxb.symm
      rw [hpEq]
    · have hbb : fR b = fR b' := by
        apply jR.injective
        calc
          jR (fR b) = lift (iR b) :=
            (functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b).symm
          _ = lift x := congrArg lift hxb.symm
          _ = lift y := hxy
          _ = lift (iR b') := congrArg lift hyb
          _ = jR (fR b') :=
            functionalLiftMap_right hSrc hTgt q fL fR
              hcompatL hcompatR b'
      have hh := hHistR K hK b b' hbb
      simpa [hxb, hyb, hpR] using hh

end IsFreeAmalgam

namespace LocallyClosedTreeCompletable

/-- Glue two full functional tree witnesses over a possibly noninjective
quotient root while retaining arbitrary finite histories in the outer
projection. -/
theorem glueIsolatedRoot_withProjectedHistory
    {BaseCarrier : Type v} {Base : Structure L BaseCarrier}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTreeL : TreeAmalgam Base ZL TL)
    (hTreeR : TreeAmalgam Base ZR TR)
    (hcL : tL.ContainedInIrreducible)
    (hcR : tR.ContainedInIrreducible)
    (q : H → G)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hrootL : IsFreeAmalgam.RootIsolated sL tL q fL)
    (hrootR : IsFreeAmalgam.RootIsolated sR tR q fR)
    (pWhole : C₀ → P) (pL : E → P) (pR : F → P) (pG : G → P)
    (hpL : ∀ x, pWhole (iL x) = pL x)
    (hpR : ∀ x, pWhole (iR x) = pR x)
    (hrootProjL : ∀ d, pL (sL d) = pG (q d))
    (hrootProjR : ∀ d, pR (sR d) = pG (q d))
    (history : List (Set P))
    (hHistL :
      ∀ K ∈ history, ∀ x y : E,
        fL x = fL y → (pL x ∈ K ↔ pL y ∈ K))
    (hHistR :
      ∀ K ∈ history, ∀ x y : F,
        fR x = fR y → (pR x ∈ K ↔ pR y ∈ K)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C₀ → Z,
        Whole.IsHomomorphismEmbedding Target f ∧
        (∀ K ∈ history, ∀ x y : C₀,
          f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K)) := by
  classical
  let Target := FreeAmalgam.amalgam Gov TL TR tL tR
  let jL := FreeAmalgam.leftEmbedding Gov TL TR tL tR
  let jR := FreeAmalgam.rightEmbedding Gov TL TR tL tR
  have hTgt : IsFreeAmalgam tL tR jL jR :=
    FreeAmalgam.isFreeAmalgam Gov TL TR tL tR
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Gov TL TR tL tR) Target :=
    FreeAmalgam.treeAmalgam Gov TL TR tL tR Base
      hTreeL hTreeR hcL hcR
  let f : C₀ → FreeAmalgam.Vertex Gov TL TR tL tR :=
    IsFreeAmalgam.functionalLiftMap hSrc hTgt q fL fR
      hcompatL hcompatR
  have hf : Whole.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  have hHist :
      ∀ K ∈ history, ∀ x y : C₀,
        f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K) :=
    IsFreeAmalgam.functionalLiftMap_respectsProjectedSets
      hSrc hTgt q fL fR hcompatL hcompatR hrootL hrootR
      pWhole pL pR pG hpL hpR hrootProjL hrootProjR
      history hHistL hHistR
  exact ⟨_, Target, hTree, f, hf, hHist⟩

end LocallyClosedTreeCompletable

end StructuralRamsey.Structure
