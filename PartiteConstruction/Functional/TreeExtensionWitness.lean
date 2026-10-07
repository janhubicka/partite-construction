import PartiteConstruction.Functional.TreeExtensionGlue
import PartiteConstruction.Functional.RelativeHistoryTreeCompletion
import PartiteConstruction.Functional.QuotientBoundaryDiary

/-! # Relative functional completions over a prescribed root tree

For a reducible closed overlap, a side witness must remember more than an
isolated copy of one irreducible control structure.  It must extend one
specific strict tree completion of the whole overlap.

`HasTreeExtensionCompletion` is that relative invariant.  It records a full
homomorphism-embedding of the side into a strict extension of a prescribed
root tree, together with exact compatibility and root isolation.  Two such
witnesses over the same root tree glue by `glueTreeExtensions`.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {VB H E G : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H} {Side : Structure L E}
variable {Start : Structure L G}

/-- A side admits a strict functional tree completion extending one prescribed
tree completion of its embedded root. -/
def HasTreeExtensionCompletion
    (s : Embedding Root Side) (q : H → G) : Prop :=
  ∃ (Z : Type v) (Target : Structure L Z)
    (hExt : TreeExtension Base Start Z Target)
    (f : E → Z),
      Side.IsHomomorphismEmbedding Target f ∧
      (∀ d, f (s d) = hExt.startEmbedding (q d)) ∧
      IsFreeAmalgam.RootIsolated
        s hExt.startEmbedding q f

namespace HasTreeExtensionCompletion

/-- The prescribed root completion extends itself.  Injectivity of the root
completion map is not needed for isolation: every collision already occurs
inside the source root. -/
theorem root
    (q : H → G)
    (hq : Root.IsHomomorphismEmbedding Start q) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start)
      (Embedding.id Root) q := by
  let hExt : TreeExtension Base Start G Start :=
    TreeExtension.refl
  refine ⟨G, Start, hExt, q, hq, ?_, ?_⟩
  · intro d
    rfl
  · intro x a hxa
    refine ⟨x, rfl, ?_⟩
    exact hxa


/-- Pull a relative completion back along a full source embedding which
commutes with the distinguished root. -/
theorem pullback_embedding
    {s : Embedding Root Side}
    {E₁ : Type v} {Side₁ : Structure L E₁}
    (j : Embedding Side₁ Side)
    (s₁ : Embedding Root Side₁)
    (hcomm : ∀ d, j (s₁ d) = s d)
    (q : H → G)
    (h :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) s q) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start) s₁ q := by
  obtain ⟨Z, Target, hExt, f, hf, hcompat, hroot⟩ := h
  let f₁ : E₁ → Z := f ∘ j
  have hf₁ : Side₁.IsHomomorphismEmbedding Target f₁ :=
    hf.comp j.isHomomorphismEmbedding
  have hcompat₁ :
      ∀ d, f₁ (s₁ d) = hExt.startEmbedding (q d) := by
    intro d
    change f (j (s₁ d)) = hExt.startEmbedding (q d)
    rw [hcomm d]
    exact hcompat d
  have hroot₁ :
      IsFreeAmalgam.RootIsolated
        s₁ hExt.startEmbedding q f₁ := by
    intro x a hxa
    have hxa' :
        f (j x) = hExt.startEmbedding a := hxa
    obtain ⟨d, hjx, hda⟩ := hroot (j x) a hxa'
    refine ⟨d, ?_, hda⟩
    apply j.injective
    calc
      j x = s d := hjx
      _ = j (s₁ d) := (hcomm d).symm
  exact ⟨Z, Target, hExt, f₁, hf₁, hcompat₁, hroot₁⟩

/-- Further strict attachments to the target preserve a relative completion. -/
theorem extendTarget
    {s : Embedding Root Side}
    (q : H → G)
    {Z₂ : Type v} {Target₂ : Structure L Z₂}
    {Z : Type v} {Target : Structure L Z}
    (hMore : TreeExtension Base Target Z₂ Target₂)
    (hTarget :
      ∃ hExt : TreeExtension Base Start Z Target,
        ∃ f : E → Z,
          Side.IsHomomorphismEmbedding Target f ∧
          (∀ d, f (s d) = hExt.startEmbedding (q d)) ∧
          IsFreeAmalgam.RootIsolated
            s hExt.startEmbedding q f) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start) s q := by
  obtain ⟨hExt, f, hf, hcompat, hroot⟩ := hTarget
  let hAll : TreeExtension Base Start Z₂ Target₂ :=
    hExt.trans hMore
  let j : Embedding Target Target₂ :=
    hMore.startEmbedding
  let f₂ : E → Z₂ := j ∘ f
  have hf₂ : Side.IsHomomorphismEmbedding Target₂ f₂ :=
    j.isHomomorphismEmbedding.comp hf
  have hcompat₂ :
      ∀ d, f₂ (s d) = hAll.startEmbedding (q d) := by
    intro d
    calc
      f₂ (s d) = j (f (s d)) := rfl
      _ = j (hExt.startEmbedding (q d)) :=
        congrArg j (hcompat d)
      _ = hAll.startEmbedding (q d) :=
        (TreeExtension.startEmbedding_trans hExt hMore (q d)).symm
  have hroot₂ :
      IsFreeAmalgam.RootIsolated
        s hAll.startEmbedding q f₂ := by
    intro x a hxa
    have hxa' :
        f x = hExt.startEmbedding a := by
      apply j.injective
      calc
        j (f x) = f₂ x := rfl
        _ = hAll.startEmbedding a := hxa
        _ = j (hExt.startEmbedding a) :=
          TreeExtension.startEmbedding_trans hExt hMore a
    exact hroot x a hxa'
  exact ⟨Z₂, Target₂, hAll, f₂, hf₂, hcompat₂, hroot₂⟩

/-- Relative completions over the same start are closed under source free
amalgamation.  The common source root remains the distinguished root of the
whole amalgam.

This is stronger than `glue`: it retains the strict extension from the
original start, so the result can be used recursively inside a larger
free-amalgam decomposition. -/
theorem glue_relative
    {F C : Type v}
    {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    {iL : Embedding Side Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (q : H → G)
    (hL :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) sL q)
    (hR :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) sR q) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start) (iL.comp sL) q := by
  classical
  obtain ⟨ZL, TL, hExtL, fL, hfL, hcompatL, hrootL⟩ := hL
  obtain ⟨ZR, TR, hExtR, fR, hfR, hcompatR, hrootR⟩ := hR
  obtain ⟨Z, Target, hAll, eL, eR, hTgt, hStartL, hStartR⟩ :=
    hExtL.mergeFree hExtR
  let f : C → Z :=
    IsFreeAmalgam.functionalLiftMap
      hSrc hTgt q fL fR hcompatL hcompatR
  have hf : Whole.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  have hcompat :
      ∀ d, f ((iL.comp sL) d) = hAll.startEmbedding (q d) := by
    intro d
    calc
      f (iL (sL d)) =
          eL (fL (sL d)) :=
        IsFreeAmalgam.functionalLiftMap_left
          hSrc hTgt q fL fR hcompatL hcompatR (sL d)
      _ = eL (hExtL.startEmbedding (q d)) :=
        congrArg eL (hcompatL d)
      _ = hAll.startEmbedding (q d) :=
        hStartL (q d)
  have hroot :
      IsFreeAmalgam.RootIsolated
        (iL.comp sL) hAll.startEmbedding q f := by
    intro x a hxa
    rcases hSrc.covers x with ⟨l, hxl⟩ | ⟨r, hxr⟩
    · have hside :
          fL l = hExtL.startEmbedding a := by
        apply eL.injective
        calc
          eL (fL l) = f (iL l) :=
            (IsFreeAmalgam.functionalLiftMap_left
              hSrc hTgt q fL fR hcompatL hcompatR l).symm
          _ = f x := congrArg f hxl.symm
          _ = hAll.startEmbedding a := hxa
          _ = eL (hExtL.startEmbedding a) :=
            (hStartL a).symm
      obtain ⟨d, hld, hda⟩ := hrootL l a hside
      refine ⟨d, ?_, hda⟩
      change x = iL (sL d)
      exact hxl.trans (congrArg iL hld)
    · have hside :
          fR r = hExtR.startEmbedding a := by
        apply eR.injective
        calc
          eR (fR r) = f (iR r) :=
            (IsFreeAmalgam.functionalLiftMap_right
              hSrc hTgt q fL fR hcompatL hcompatR r).symm
          _ = f x := congrArg f hxr.symm
          _ = hAll.startEmbedding a := hxa
          _ = eR (hExtR.startEmbedding a) :=
            (hStartR a).symm
      obtain ⟨d, hrd, hda⟩ := hrootR r a hside
      refine ⟨d, ?_, hda⟩
      change x = iL (sL d)
      calc
        x = iR r := hxr
        _ = iR (sR d) := congrArg iR hrd
        _ = iL (sL d) :=
          ((hSrc.overlap (sL d) (sR d)).mpr
            ⟨d, rfl, rfl⟩).symm
  exact ⟨Z, Target, hAll, f, hf, hcompat, hroot⟩


/-- Rebase a relative completion along a further strict extension of the
common root tree.

The side target is replayed over the larger start.  Exact free-amalgam
overlap supplied by `replayFree` transports root isolation: any side point
landing in the new start must already have landed in the old start. -/
theorem rebase
    {s : Embedding Root Side}
    {G₂ : Type v} {Start₂ : Structure L G₂}
    (q : H → G)
    (h :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) s q)
    (hMore : TreeExtension Base Start G₂ Start₂) :
    HasTreeExtensionCompletion
      (Base := Base) (Start := Start₂) s
      (hMore.startEmbedding ∘ q) := by
  classical
  obtain ⟨Z, Target, hExt, f, hf, hcompat, hroot⟩ := h
  obtain ⟨Z₂, Target₂, hExt₂, e, hFree, hStart⟩ :=
    hExt.replayFree hMore.startEmbedding
  let f₂ : E → Z₂ := e ∘ f
  have hf₂ : Side.IsHomomorphismEmbedding Target₂ f₂ :=
    e.isHomomorphismEmbedding.comp hf
  have hcompat₂ :
      ∀ d, f₂ (s d) =
        hExt₂.startEmbedding ((hMore.startEmbedding ∘ q) d) := by
    intro d
    calc
      f₂ (s d) = e (f (s d)) := rfl
      _ = e (hExt.startEmbedding (q d)) :=
        congrArg e (hcompat d)
      _ = hExt₂.startEmbedding (hMore.startEmbedding (q d)) :=
        hStart (q d)
      _ = hExt₂.startEmbedding ((hMore.startEmbedding ∘ q) d) := rfl
  have hroot₂ :
      IsFreeAmalgam.RootIsolated
        s hExt₂.startEmbedding (hMore.startEmbedding ∘ q) f₂ := by
    intro x a hxa
    have hmeet :
        hExt₂.startEmbedding a = e (f x) :=
      hxa.symm
    obtain ⟨b, hab, hfb⟩ :=
      (hFree.overlap a (f x)).mp hmeet
    obtain ⟨d, hxd, hdb⟩ :=
      hroot x b hfb
    refine ⟨d, hxd, ?_⟩
    calc
      (hMore.startEmbedding ∘ q) d =
          hMore.startEmbedding (q d) := rfl
      _ = hMore.startEmbedding b :=
        congrArg hMore.startEmbedding hdb
      _ = a := hab.symm
  exact ⟨Z₂, Target₂, hExt₂, f₂, hf₂, hcompat₂, hroot₂⟩


/-- Two side completions relative to the same strict root tree glue to a full
completion of their source free amalgam. -/
theorem glue
    {F C : Type v}
    {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    {iL : Embedding Side Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hStart : TreeAmalgam Base G Start)
    (q : H → G)
    (hL :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) sL q)
    (hR :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) sR q) :
    HasTreeCompletion Base Whole := by
  obtain ⟨ZL, TL, hExtL, fL, hfL, hcompatL, hrootL⟩ := hL
  obtain ⟨ZR, TR, hExtR, fR, hfR, hcompatR, hrootR⟩ := hR
  exact
    LocallyClosedTreeCompletable.glueTreeExtensions
      hSrc hStart hExtL hExtR q
      fL fR hcompatL hcompatR hfL hfR hrootL hrootR

end HasTreeExtensionCompletion


/-- Two sides have compatible strict completions over one common tree
completion of their source root.  This is the natural induction output for a
mixed functional free-amalgam step with a reducible overlap. -/
def HasCommonRootedCompletions
    {F : Type v} {Right : Structure L F}
    (sL : Embedding Root Side) (sR : Embedding Root Right) : Prop :=
  ∃ (G₀ : Type v) (Start₀ : Structure L G₀),
    TreeAmalgam Base G₀ Start₀ ∧
    ∃ q : H → G₀,
      Root.IsHomomorphismEmbedding Start₀ q ∧
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start₀) sL q ∧
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start₀) sR q

namespace HasCommonRootedCompletions

/-- Compatible rooted side completions immediately give a strict completion of
their source free amalgam. -/
theorem glue
    {F C : Type v}
    {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    {iL : Embedding Side Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (h :
      HasCommonRootedCompletions
        (Base := Base) sL sR) :
    HasTreeCompletion Base Whole := by
  obtain ⟨G₀, Start₀, hStart, q, _hq, hL, hR⟩ := h
  exact HasTreeExtensionCompletion.glue
    hSrc hStart q hL hR


end HasCommonRootedCompletions



/-- An isolated quotient-labelled boundary can be standardized to a relative
completion rooted at the fixed Base itself.

No injectivity of the quotient label is required.  Attach one fresh Base copy
to the side target along the isolated A-copy, then reroot the resulting strict
tree at that fresh Base copy.  Root isolation is inherited from the quotient
boundary certificate and exactness of the free-amalgam overlap. -/
theorem HasTreeExtensionCompletion.of_isolatedQuotientBoundary_rootedBase
    {U W V Y : Type v}
    {A : Structure L U} {C : Structure L W}
    {Base₀ : Structure L V} {T : Structure L Y}
    [Finite V]
    (hA : A.Irreducible)
    (hBase : Base₀.Irreducible)
    (eAB : Embedding A Base₀)
    (r : QuotientBoundaryRequest A C)
    (hTree : TreeAmalgam Base₀ Y T)
    (f : W → Y)
    (hf : C.IsHomomorphismEmbedding T f)
    (hIso : IsolatedQuotientBoundary r T f) :
    HasTreeExtensionCompletion
      (Base := Base₀) (Start := Base₀)
      r.embedding (fun x => eAB (r.label x)) := by
  classical
  obtain ⟨targetCopy, hcompat, hroot⟩ := hIso
  have hcT : targetCopy.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetCopy, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcB : eAB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro a
    exact ⟨a, rfl⟩

  let T1 := FreeAmalgam.amalgam A T Base₀ targetCopy eAB
  let l : Embedding T T1 :=
    FreeAmalgam.leftEmbedding A T Base₀ targetCopy eAB
  let rb : Embedding Base₀ T1 :=
    FreeAmalgam.rightEmbedding A T Base₀ targetCopy eAB
  have hfree : IsFreeAmalgam targetCopy eAB l rb :=
    FreeAmalgam.isFreeAmalgam A T Base₀ targetCopy eAB
  have hTree1 : TreeAmalgam Base₀ _ T1 :=
    FreeAmalgam.treeAmalgam A T Base₀ targetCopy eAB Base₀
      hTree
      (TreeAmalgam.copy (Embedding.id Base₀) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB

  let f1 : W → _ := l ∘ f
  have hf1 : C.IsHomomorphismEmbedding T1 f1 :=
    l.isHomomorphismEmbedding.comp hf
  have hcompat1 :
      ∀ x : r.Carrier,
        f1 (r.embedding x) = rb (eAB (r.label x)) := by
    intro x
    change l (f (r.embedding x)) = rb (eAB (r.label x))
    calc
      l (f (r.embedding x)) =
          l (targetCopy (r.label x)) :=
        congrArg l (hcompat x)
      _ = rb (eAB (r.label x)) :=
        (hfree.overlap
          (targetCopy (r.label x))
          (eAB (r.label x))).mpr
            ⟨r.label x, rfl, rfl⟩

  have hroot1 :
      IsFreeAmalgam.RootIsolated
        r.embedding rb (fun x => eAB (r.label x)) f1 := by
    intro y b hyb
    change l (f y) = rb b at hyb
    obtain ⟨a, hfa, hba⟩ :=
      (hfree.overlap (f y) b).mp hyb
    obtain ⟨x, hyx, hxa⟩ := hroot y a hfa
    refine ⟨x, hyx, ?_⟩
    calc
      eAB (r.label x) = eAB a :=
        congrArg eAB hxa
      _ = b := hba.symm

  obtain ⟨Z2, T2, hExt, j, hj⟩ :=
    TreeExtension.embedIntoRootedExtension
      hBase hTree1 rb
  let f2 : W → Z2 := j ∘ f1
  have hf2 : C.IsHomomorphismEmbedding T2 f2 :=
    j.isHomomorphismEmbedding.comp hf1
  have hcompat2 :
      ∀ x : r.Carrier,
        f2 (r.embedding x) =
          hExt.startEmbedding (eAB (r.label x)) := by
    intro x
    calc
      f2 (r.embedding x) = j (f1 (r.embedding x)) := rfl
      _ = j (rb (eAB (r.label x))) :=
        congrArg j (hcompat1 x)
      _ = hExt.startEmbedding (eAB (r.label x)) :=
        hj (eAB (r.label x))
  have hroot2 :
      IsFreeAmalgam.RootIsolated
        r.embedding hExt.startEmbedding
        (fun x => eAB (r.label x)) f2 := by
    intro y b hyb
    have hyb1 : f1 y = rb b := by
      apply j.injective
      calc
        j (f1 y) = f2 y := rfl
        _ = hExt.startEmbedding b := hyb
        _ = j (rb b) := (hj b).symm
    exact hroot1 y b hyb1

  exact ⟨Z2, T2, hExt, f2, hf2, hcompat2, hroot2⟩

namespace HasCommonRootedCompletions

/-- If the same quotient-labelled root is isolated in two side witnesses, the
two sides have compatible rooted completions with the fixed Base as common
start.  The quotient label may be noninjective. -/
theorem of_isolatedQuotientBoundaries_rootedBase
    {U F YL YR : Type v}
    {A : Structure L U}
    {Right : Structure L F}
    {TL : Structure L YL} {TR : Structure L YR}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    [Finite VB]
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    (label : H → U)
    (hTreeL : TreeAmalgam Base YL TL)
    (hTreeR : TreeAmalgam Base YR TR)
    (fL : E → YL) (fR : F → YR)
    (hfL : Side.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hIsoL :
      IsolatedQuotientBoundary
        (QuotientBoundaryRequest.ofEmbedding (A := A) sL label) TL fL)
    (hIsoR :
      IsolatedQuotientBoundary
        (QuotientBoundaryRequest.ofEmbedding (A := A) sR label) TR fR) :
    HasCommonRootedCompletions
      (Base := Base) sL sR := by
  let rL : QuotientBoundaryRequest A Side :=
    QuotientBoundaryRequest.ofEmbedding sL label
  let rR : QuotientBoundaryRequest A Right :=
    QuotientBoundaryRequest.ofEmbedding sR label
  let q : H → VB := fun x => eAB (label x)
  have hLabel :
      Root.IsHomomorphismEmbedding A label := by
    simpa [rL, QuotientBoundaryRequest.ofEmbedding] using
      (IsolatedQuotientBoundary.label_isHomomorphismEmbedding
        hIsoL hfL)
  have hq :
      Root.IsHomomorphismEmbedding Base q := by
    exact eAB.isHomomorphismEmbedding.comp hLabel
  have hStart : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro b
      exact ⟨b, rfl⟩)
  have hL :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Base) sL q := by
    simpa [rL, q, QuotientBoundaryRequest.ofEmbedding] using
      (HasTreeExtensionCompletion.of_isolatedQuotientBoundary_rootedBase
        hA hBase eAB rL hTreeL fL hfL hIsoL)
  have hR :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Base) sR q := by
    simpa [rR, q, QuotientBoundaryRequest.ofEmbedding] using
      (HasTreeExtensionCompletion.of_isolatedQuotientBoundary_rootedBase
        hA hBase eAB rR hTreeR fR hfR hIsoR)
  exact ⟨VB, Base, hStart, q, hq, hL, hR⟩

end HasCommonRootedCompletions


namespace FunctionalRelativeHistoryTreeLike

variable {U P W V X : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base₀ : Structure L V}
variable {p : W → P} {n : ℕ}

/-- An embedded-labelled relative-history witness can be standardized to a
tree extension rooted at the fixed Base itself.

After obtaining the isolated target A-copy, attach one fresh Base-copy along
it using eAB.  Reroot the resulting strict tree at that fresh Base-copy.  The
distinguished source boundary then has the fixed Base-label
\`eAB ∘ ell\`, independently of how the original target tree was built. -/
theorem fullWitness_rootedBase
    [Fintype W] [Finite V]
    (hA : A.Irreducible)
    (hBase : Base₀.Irreducible)
    (eAB : Embedding A Base₀)
    (h :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := C) (Base := Base₀) p n)
    (hgen : C.GeneratedByAtMost n)
    {R : Structure L X}
    (ell : Embedding R A)
    (β : Embedding A D)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = β (ell x)) :
    HasTreeExtensionCompletion
      (Base := Base₀) (Start := Base₀)
      e (fun x => eAB (ell x)) := by
  classical
  obtain ⟨Z, T, hTree, f, hf, _hPart, _hProj, _hSrc,
    targetCopy, hcompat, hiso⟩ :=
    h.fullWitness_embeddedLabels
      hgen [] [] ell β e hproj

  have hcT : targetCopy.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetCopy, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcB : eAB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro a
    exact ⟨a, rfl⟩

  let T1 := FreeAmalgam.amalgam A T Base₀ targetCopy eAB
  let l : Embedding T T1 :=
    FreeAmalgam.leftEmbedding A T Base₀ targetCopy eAB
  let r : Embedding Base₀ T1 :=
    FreeAmalgam.rightEmbedding A T Base₀ targetCopy eAB
  have hfree : IsFreeAmalgam targetCopy eAB l r :=
    FreeAmalgam.isFreeAmalgam A T Base₀ targetCopy eAB
  have hTree1 : TreeAmalgam Base₀ _ T1 :=
    FreeAmalgam.treeAmalgam A T Base₀ targetCopy eAB Base₀
      hTree
      (TreeAmalgam.copy (Embedding.id Base₀) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB

  let f1 : W → _ := l ∘ f
  have hf1 : C.IsHomomorphismEmbedding T1 f1 :=
    l.isHomomorphismEmbedding.comp hf
  have hcompat1 :
      ∀ x : X, f1 (e x) = r (eAB (ell x)) := by
    intro x
    change l (f (e x)) = r (eAB (ell x))
    calc
      l (f (e x)) = l (targetCopy (ell x)) :=
        congrArg l (hcompat x)
      _ = r (eAB (ell x)) :=
        (hfree.overlap (targetCopy (ell x)) (eAB (ell x))).mpr
          ⟨ell x, rfl, rfl⟩

  have hroot1 :
      IsFreeAmalgam.RootIsolated
        e r (fun x => eAB (ell x)) f1 := by
    intro y b hyb
    change l (f y) = r b at hyb
    obtain ⟨a, hfa, hba⟩ :=
      (hfree.overlap (f y) b).mp hyb
    obtain ⟨x, hyx, hxa⟩ := hiso y a hfa
    refine ⟨x, hyx, ?_⟩
    calc
      eAB (ell x) = eAB a := congrArg eAB hxa
      _ = b := hba.symm

  obtain ⟨Z2, T2, hExt, j, hj⟩ :=
    TreeExtension.embedIntoRootedExtension
      hBase hTree1 r
  let f2 : W → Z2 := j ∘ f1
  have hf2 : C.IsHomomorphismEmbedding T2 f2 :=
    j.isHomomorphismEmbedding.comp hf1
  have hcompat2 :
      ∀ x : X,
        f2 (e x) =
          hExt.startEmbedding (eAB (ell x)) := by
    intro x
    calc
      f2 (e x) = j (f1 (e x)) := rfl
      _ = j (r (eAB (ell x))) :=
        congrArg j (hcompat1 x)
      _ = hExt.startEmbedding (eAB (ell x)) :=
        hj (eAB (ell x))
  have hroot2 :
      IsFreeAmalgam.RootIsolated
        e hExt.startEmbedding (fun x => eAB (ell x)) f2 := by
    intro y b hyb
    have hyb1 : f1 y = r b := by
      apply j.injective
      calc
        j (f1 y) = f2 y := rfl
        _ = hExt.startEmbedding b := hyb
        _ = j (r b) := (hj b).symm
    exact hroot1 y b hyb1

  exact ⟨Z2, T2, hExt, f2, hf2, hcompat2, hroot2⟩


/-- If the common root genuinely embeds into one A-copy, two relative-history
side invariants produce compatible rooted completions with the fixed Base as
their common start.  This is the terminal branch of the reducible-root
induction. -/
theorem commonRootedCompletions_embeddedLabels
    {F H₀ : Type v}
    {Right : Structure L F}
    {Root₀ : Structure L H₀}
    {sL : Embedding Root₀ C}
    {sR : Embedding Root₀ Right}
    {pR : F → P}
    [Fintype W] [Fintype F] [Finite V]
    (hA : A.Irreducible)
    (hBase : Base₀.Irreducible)
    (eAB : Embedding A Base₀)
    (hL :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := C) (Base := Base₀) p n)
    (hR :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := Right) (Base := Base₀) pR n)
    (hgenL : C.GeneratedByAtMost n)
    (hgenR : Right.GeneratedByAtMost n)
    (ell : Embedding Root₀ A)
    (β : Embedding A D)
    (hprojL : ∀ x, p (sL x) = β (ell x))
    (hprojR : ∀ x, pR (sR x) = β (ell x)) :
    HasCommonRootedCompletions
      (Base := Base₀) sL sR := by
  let q : H₀ → V := fun x => eAB (ell x)
  have hq : Root₀.IsHomomorphismEmbedding Base₀ q :=
    eAB.isHomomorphismEmbedding.comp ell.isHomomorphismEmbedding
  have hTreeBase : TreeAmalgam Base₀ V Base₀ :=
    TreeAmalgam.copy (Embedding.id Base₀) (by
      intro b
      exact ⟨b, rfl⟩)
  have hLeft :
      HasTreeExtensionCompletion
        (Base := Base₀) (Start := Base₀) sL q :=
    hL.fullWitness_rootedBase
      hA hBase eAB hgenL ell β sL hprojL
  have hRight :
      HasTreeExtensionCompletion
        (Base := Base₀) (Start := Base₀) sR q :=
    hR.fullWitness_rootedBase
      hA hBase eAB hgenR ell β sR hprojR
  exact ⟨V, Base₀, hTreeBase, q, hq, hLeft, hRight⟩

end FunctionalRelativeHistoryTreeLike

end StructuralRamsey.Structure
