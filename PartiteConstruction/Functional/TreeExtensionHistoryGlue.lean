import PartiteConstruction.Functional.TreeExtensionGlue
import PartiteConstruction.Functional.QuotientProjectedHistoryGlue

/-! # Projected histories in strict tree-extension gluing

The common root of a functional mixed attachment may be reducible and its
completion may identify vertices.  Strict extensions of one common root tree
can nevertheless be merged with an exact target free-amalgam certificate.
Projected histories survive that merge provided the outer projection on
the source root factors through the chosen completion map.

Unlike source-side histories, projected histories do not require the root
completion map to be injective.  This is the gluing interface required by
the reducible-root branch of the closure-aware iteration.
-/

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {VB H E F C G ZL ZR P : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {Start : Structure L G}
variable {TL : Structure L ZL} {TR : Structure L ZR}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Glue two strict tree extensions of the same root completion, retaining
arbitrary projected histories even when the root map is noninjective.
Root isolation prevents identifications with points outside the overlap. -/
theorem glueTreeExtensions_withProjectedHistory
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hStart : TreeAmalgam Base G Start)
    (hExtL : TreeExtension Base Start ZL TL)
    (hExtR : TreeExtension Base Start ZR TR)
    (q : H → G)
    (fL : E → ZL) (fR : F → ZR)
    (hcompatL : ∀ d, fL (sL d) = hExtL.startEmbedding (q d))
    (hcompatR : ∀ d, fR (sR d) = hExtR.startEmbedding (q d))
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hrootL :
      IsFreeAmalgam.RootIsolated sL hExtL.startEmbedding q fL)
    (hrootR :
      IsFreeAmalgam.RootIsolated sR hExtR.startEmbedding q fR)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (pG : G → P)
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
      ∃ f : C → Z,
        Whole.IsHomomorphismEmbedding Target f ∧
        (∀ K ∈ history, ∀ x y : C,
          f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K)) := by
  obtain ⟨Z, Target, hTree, eL, eR, hTgt⟩ :=
    hExtL.mergeFree_tree hStart hExtR
  let f : C → Z :=
    IsFreeAmalgam.functionalLiftMap
      hSrc hTgt q fL fR hcompatL hcompatR
  have hf : Whole.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  have hHist :
      ∀ K ∈ history, ∀ x y : C,
        f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K) :=
    IsFreeAmalgam.functionalLiftMap_respectsProjectedSets
      hSrc hTgt q fL fR hcompatL hcompatR hrootL hrootR
      pWhole pL pR pG hpL hpR hrootProjL hrootProjR
      history hHistL hHistR
  exact ⟨Z, Target, hTree, f, hf, hHist⟩

end StructuralRamsey.Structure.LocallyClosedTreeCompletable
