import PartiteConstruction.Functional.TreeExtensionHistoryInduction

/-! # Embedded A-boundaries as strict relative trees, with projected history

The embedded-label case is the terminal case of the reducible-root induction.
The existing rooted-base construction creates a strict extension of a fixed
Base-copy, but did not retain the projected histories requested by later
Picture steps.  Here the histories are taken through the same sequence of
injective target embeddings.  This also supplies a common completed root
for two sides whenever their labels agree in the outer structure.
-/

namespace StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike

universe u v

variable {L : Language.{u}}
variable {U P W V X : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}
variable {p : W → P} {n : ℕ}

/-- An embedded-labelled relative-history witness can be rooted at the
fixed Base-copy while retaining every requested projected history. -/
theorem fullWitness_rootedBase_withHistory
    [Fintype W] [Finite V]
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hgen : C.GeneratedByAtMost n)
    {R : Structure L X}
    (ell : Embedding R A)
    (β : Embedding A D)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = β (ell x))
    (projectedHistory : List (Set P)) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Base)
      e (fun x => eAB (ell x)) p projectedHistory := by
  classical
  obtain ⟨Z, T, hTree, f, hf, _hPart, hProj, _hSrc,
    targetCopy, hcompat, hiso⟩ :=
    h.fullWitness_embeddedLabels
      hgen projectedHistory [] ell β e hproj

  have hcT : targetCopy.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetCopy, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcB : eAB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro a
    exact ⟨a, rfl⟩

  let T1 := FreeAmalgam.amalgam A T Base targetCopy eAB
  let l : Embedding T T1 :=
    FreeAmalgam.leftEmbedding A T Base targetCopy eAB
  let r : Embedding Base T1 :=
    FreeAmalgam.rightEmbedding A T Base targetCopy eAB
  have hfree : IsFreeAmalgam targetCopy eAB l r :=
    FreeAmalgam.isFreeAmalgam A T Base targetCopy eAB
  have hTree1 : TreeAmalgam Base _ T1 :=
    FreeAmalgam.treeAmalgam A T Base targetCopy eAB Base
      hTree
      (TreeAmalgam.copy (Embedding.id Base) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB

  let f1 : W → _ := l ∘ f
  have hf1 : C.IsHomomorphismEmbedding T1 f1 :=
    l.isHomomorphismEmbedding.comp hf
  have hcompat1 : ∀ x : X, f1 (e x) = r (eAB (ell x)) := by
    intro x
    change l (f (e x)) = r (eAB (ell x))
    calc
      l (f (e x)) = l (targetCopy (ell x)) :=
        congrArg l (hcompat x)
      _ = r (eAB (ell x)) :=
        (hfree.overlap (targetCopy (ell x)) (eAB (ell x))).mpr
          ⟨ell x, rfl, rfl⟩
  have hroot1 : IsFreeAmalgam.RootIsolated
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
    TreeExtension.embedIntoRootedExtension hBase hTree1 r
  let f2 : W → Z2 := j ∘ f1
  have hf2 : C.IsHomomorphismEmbedding T2 f2 :=
    j.isHomomorphismEmbedding.comp hf1
  have hcompat2 : ∀ x : X,
      f2 (e x) = hExt.startEmbedding (eAB (ell x)) := by
    intro x
    calc
      f2 (e x) = j (f1 (e x)) := rfl
      _ = j (r (eAB (ell x))) := congrArg j (hcompat1 x)
      _ = hExt.startEmbedding (eAB (ell x)) := hj (eAB (ell x))
  have hroot2 : IsFreeAmalgam.RootIsolated
      e hExt.startEmbedding (fun x => eAB (ell x)) f2 := by
    intro y b hyb
    have hyb1 : f1 y = r b := by
      apply j.injective
      calc
        j (f1 y) = f2 y := rfl
        _ = hExt.startEmbedding b := hyb
        _ = j (r b) := (hj b).symm
    exact hroot1 y b hyb1

  have hProj2 :
      ∀ Hset ∈ projectedHistory, ∀ x y : W,
        f2 x = f2 y → (p x ∈ Hset ↔ p y ∈ Hset) := by
    intro Hset hmem x y hxy
    apply hProj Hset hmem x y
    apply l.injective
    apply j.injective
    exact hxy

  exact ⟨Z2, T2, hExt, f2, hf2, hcompat2, hroot2, hProj2⟩

/-- Two sides with a common full A-labelling admit a synchronized strict
Base-root completion, including arbitrary finite projected histories.
The map from Base into the outer carrier is supplied by the actual
partite projection, so no nonemptiness choice is hidden here. -/
theorem commonRootedProjectedHistory_embeddedLabels
    {F H₀ : Type v}
    {Right : Structure L F}
    {Root₀ : Structure L H₀}
    {sL : Embedding Root₀ C}
    {sR : Embedding Root₀ Right}
    {pR : F → P}
    [Fintype W] [Fintype F] [Finite V]
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    (hL : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hR : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := Right) (Base := Base) pR n)
    (hgenL : C.GeneratedByAtMost n)
    (hgenR : Right.GeneratedByAtMost n)
    (ell : Embedding Root₀ A)
    (β : Embedding A D)
    (hprojL : ∀ x, p (sL x) = β (ell x))
    (hprojR : ∀ x, pR (sR x) = β (ell x))
    (pBase : V → P)
    (hBaseLabels : ∀ a, pBase (eAB a) = β a)
    (history : List (Set P)) :
    HasCommonRootedProjectedHistoryCompletions
      (Base := Base) sL sR p pR history := by
  let q : H₀ → V := fun x => eAB (ell x)
  have hq : Root₀.IsHomomorphismEmbedding Base q :=
    eAB.isHomomorphismEmbedding.comp ell.isHomomorphismEmbedding
  have hTreeBase : TreeAmalgam Base V Base :=
    TreeAmalgam.copy (Embedding.id Base) (by
      intro b
      exact ⟨b, rfl⟩)
  have hrootProjL : ∀ d, p (sL d) = pBase (q d) := by
    intro d
    calc
      p (sL d) = β (ell d) := hprojL d
      _ = pBase (eAB (ell d)) := (hBaseLabels (ell d)).symm
  have hrootProjR : ∀ d, pR (sR d) = pBase (q d) := by
    intro d
    calc
      pR (sR d) = β (ell d) := hprojR d
      _ = pBase (eAB (ell d)) := (hBaseLabels (ell d)).symm
  have hLeft : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Base) sL q p history :=
    hL.fullWitness_rootedBase_withHistory
      hA hBase eAB hgenL ell β sL hprojL history
  have hRight : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Base) sR q pR history :=
    hR.fullWitness_rootedBase_withHistory
      hA hBase eAB hgenR ell β sR hprojR history
  exact ⟨V, Base, hTreeBase, q, hq, pBase,
    hrootProjL, hrootProjR, hLeft, hRight⟩

end StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike
