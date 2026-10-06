import PartiteConstruction.Functional.TreeExtensionGlue
import PartiteConstruction.Functional.RelativeHistoryTreeCompletion

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
    (q : H → G)
    (h :
      HasTreeExtensionCompletion
        (Base := Base) (Start := Start) s q)
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

end FunctionalRelativeHistoryTreeLike

end StructuralRamsey.Structure
