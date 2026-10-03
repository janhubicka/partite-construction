import PartiteConstruction.Iterated.IntersectionStrongLocalTreeLike
import PartiteConstruction.Iterated.WitnessGlueContained

/-! # Projected gluing from intersection-strong witnesses

Intersection-strong witnesses make the projected overlap an actual embedded
substructure on both sides, even when it is reducible.  Since those embedded
images also lie inside controlled A-copies, the tree targets may be glued
over that reducible overlap using the contained-overlap tree-amalgam rule.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H E F C P : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Dsrc : RelStructure L H} {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F} {Csrc : RelStructure L C}
variable {D : RelStructure L P}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Strong control data for one projected finite image. -/
def ProjectedIntersectionControl
    (I : Finset P) {T : Type v} (Target : RelStructure L T)
    (g : ↥(↑I : Set P) → T) : Prop :=
  ∀ α : Embedding Control D,
    ∃ α' : Embedding Control Target,
      (∀ a : UA, ∀ ha : α a ∈ I,
        ∃ a' : UA, g ⟨α a, ha⟩ = α' a') ∧
      ∃ h : Embedding (Control.induce {a : UA | α a ∈ I}) Target,
        ∀ x, h x = g ⟨α x.1, x.2⟩

/-- Glue projected side witnesses while retaining their strong projected
control in the common target. -/
theorem glueProjectedFull_intersectionStrong
    [Fintype E] [Fintype F] [DecidableEq P]
    (hControl : Control.Irreducible)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (p : C → P) (hp : Csrc.IsHomomorphismEmbedding D p)
    (α : Embedding Control D)
    (hOverlap : ∀ d : H, ∃ a : UA, p (iE (sE d)) = α a)
    (m : ℕ)
    (hD : IntersectionStrongLocallyTreeLike Control Base D m)
    (hEcard : ((Finset.univ : Finset E).image (p ∘ iE)).card ≤ m)
    (hFcard : ((Finset.univ : Finset F).image (p ∘ iF)).card ≤ m) :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∃ Eimg : Finset P, ∃ Fimg : Finset P,
          ∃ gE : ↥(↑Eimg : Set P) → T,
          ∃ gF : ↥(↑Fimg : Set P) → T,
            ProjectedIntersectionControl
                (Control := Control) (D := D) Eimg Target gE ∧
            ProjectedIntersectionControl
                (Control := Control) (D := D) Fimg Target gF ∧
            (∀ e : E,
              f (iE e) =
                gE ⟨p (iE e),
                  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩) ∧
            (∀ e : F,
              f (iF e) =
                gF ⟨p (iF e),
                  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩) := by
  classical
  let pE : E → P := p ∘ iE
  let pF : F → P := p ∘ iF
  let Eimg : Finset P := (Finset.univ : Finset E).image pE
  let Fimg : Finset P := (Finset.univ : Finset F).image pF
  obtain ⟨TE, TEs, hTreeE, gE0, hgE, ctrlE⟩ := hD Eimg hEcard
  obtain ⟨TF, TFs, hTreeF, gF0, hgF, ctrlF⟩ := hD Fimg hFcard

  let pEsub : E → ↥(↑Eimg : Set P) :=
    fun e => ⟨pE e, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
  let pFsub : F → ↥(↑Fimg : Set P) :=
    fun e => ⟨pF e, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
  have hpE : Esrc.IsHomomorphismEmbedding D pE :=
    hp.comp iE.isHomomorphismEmbedding
  have hpF : Fsrc.IsHomomorphismEmbedding D pF :=
    hp.comp iF.isHomomorphismEmbedding
  have hpEsub :
      Esrc.IsHomomorphismEmbedding (D.induce (↑Eimg : Set P)) pEsub := by
    exact hpE.codRestrict (↑Eimg : Set P)
      (fun e => Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
  have hpFsub :
      Fsrc.IsHomomorphismEmbedding (D.induce (↑Fimg : Set P)) pFsub := by
    exact hpF.codRestrict (↑Fimg : Set P)
      (fun e => Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
  let fE : E → TE := gE0 ∘ pEsub
  let fF : F → TF := gF0 ∘ pFsub
  have hfE : Esrc.IsHomomorphismEmbedding TEs fE := hgE.comp hpEsub
  have hfF : Fsrc.IsHomomorphismEmbedding TFs fF := hgF.comp hpFsub

  let q0 : H → P := fun d => p (iE (sE d))
  let Gset : Set P := Set.range q0
  let Gov : RelStructure L Gset := D.induce Gset
  have hqF (d : H) : q0 d = pF (sF d) := by
    change p (iE (sE d)) = p (iF (sF d))
    apply congrArg p
    exact (hSrc.overlap (sE d) (sF d)).mpr ⟨d, rfl, rfl⟩
  let incGD : Embedding Gov D := inclusion D Gset
  have hGalpha : ∀ z : Gset, ∃ a : UA, incGD z = α a := by
    intro z
    rcases z.2 with ⟨d, hd⟩
    obtain ⟨a, ha⟩ := hOverlap d
    exact ⟨a, hd.symm.trans ha⟩
  let eGA : Embedding Gov Control :=
    incGD.factorThroughRange α hGalpha
  have heGA (z : Gset) : α (eGA z) = z.1 := by
    have hz := Classical.choose_spec (hGalpha z)
    exact hz.symm

  let incGE : Embedding Gov (D.induce (↑Eimg : Set P)) := {
    toFun := fun z => ⟨z.1, by
      rcases z.2 with ⟨d, hd⟩
      apply Finset.mem_image.mpr
      refine ⟨sE d, Finset.mem_univ _, ?_⟩
      change pE (sE d) = z.1
      exact hd⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let incGF : Embedding Gov (D.induce (↑Fimg : Set P)) := {
    toFun := fun z => ⟨z.1, by
      rcases z.2 with ⟨d, hd⟩
      apply Finset.mem_image.mpr
      refine ⟨sF d, Finset.mem_univ _, ?_⟩
      change pF (sF d) = z.1
      rw [← hqF d]
      exact hd⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => Iff.rfl
  }

  obtain ⟨αTE, hαTE, hitE, hhitE⟩ := ctrlE α
  obtain ⟨αTF, hαTF, hitF, hhitF⟩ := ctrlF α
  let HitE : Set UA := {a : UA | α a ∈ Eimg}
  let HitF : Set UA := {a : UA | α a ∈ Fimg}
  let eGHitE : Embedding Gov (Control.induce HitE) := {
    toFun := fun z => ⟨eGA z, by
      change α (eGA z) ∈ Eimg
      rw [heGA z]
      exact (incGE z).2⟩
    injective := by
      intro x y hxy
      apply eGA.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := fun R x => eGA.map_rel_iff R x
  }
  let eGHitF : Embedding Gov (Control.induce HitF) := {
    toFun := fun z => ⟨eGA z, by
      change α (eGA z) ∈ Fimg
      rw [heGA z]
      exact (incGF z).2⟩
    injective := by
      intro x y hxy
      apply eGA.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := fun R x => eGA.map_rel_iff R x
  }
  let tE : Embedding Gov TEs := hitE.comp eGHitE
  let tF : Embedding Gov TFs := hitF.comp eGHitF
  have htE (z : Gset) : tE z = gE0 (incGE z) := by
    change hitE (eGHitE z) = gE0 (incGE z)
    rw [hhitE (eGHitE z)]
    apply congrArg gE0
    apply Subtype.ext
    exact heGA z
  have htF (z : Gset) : tF z = gF0 (incGF z) := by
    change hitF (eGHitF z) = gF0 (incGF z)
    rw [hhitF (eGHitF z)]
    apply congrArg gF0
    apply Subtype.ext
    exact heGA z
  have hcE : tE.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset hControl αTE tE
    intro z
    have hzmem : α (eGA z) ∈ Eimg := by
      rw [heGA z]
      exact (incGE z).2
    obtain ⟨a', ha'⟩ := hαTE (eGA z) hzmem
    refine ⟨a', ?_⟩
    rw [htE z]
    have heq :
        (⟨α (eGA z), hzmem⟩ : ↥(↑Eimg : Set P)) = incGE z := by
      apply Subtype.ext
      exact heGA z
    rw [← heq]
    exact ha'
  have hcF : tF.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset hControl αTF tF
    intro z
    have hzmem : α (eGA z) ∈ Fimg := by
      rw [heGA z]
      exact (incGF z).2
    obtain ⟨a', ha'⟩ := hαTF (eGA z) hzmem
    refine ⟨a', ?_⟩
    rw [htF z]
    have heq :
        (⟨α (eGA z), hzmem⟩ : ↥(↑Fimg : Set P)) = incGF z := by
      apply Subtype.ext
      exact heGA z
    rw [← heq]
    exact ha'

  let q : H → Gset := fun d => ⟨q0 d, ⟨d, rfl⟩⟩
  have hcompatE : ∀ d, fE (sE d) = tE (q d) := by
    intro d
    rw [htE (q d)]
    apply congrArg gE0
    apply Subtype.ext
    rfl
  have hcompatF : ∀ d, fF (sF d) = tF (q d) := by
    intro d
    rw [htF (q d)]
    apply congrArg gF0
    apply Subtype.ext
    exact (hqF d).symm

  let Target := FreeAmalgam.amalgam Gov TEs TFs tE tF
  let jE := FreeAmalgam.leftEmbedding Gov TEs TFs tE tF
  let jF := FreeAmalgam.rightEmbedding Gov TEs TFs tE tF
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Gov TEs TFs tE tF) Target :=
    FreeAmalgam.treeAmalgam Gov TEs TFs tE tF Base
      hTreeE hTreeF hcE hcF
  have hTgt : IsFreeAmalgam tE tF jE jF :=
    FreeAmalgam.isFreeAmalgam Gov TEs TFs tE tF
  let fOut : C → FreeAmalgam.Vertex Gov TEs TFs tE tF :=
    IsFreeAmalgam.liftMap hSrc hTgt q fE fF hcompatE hcompatF
  have hfOut : Csrc.IsHomomorphismEmbedding Target fOut :=
    IsFreeAmalgam.liftMap_isHomomorphismEmbedding
      hSrc hTgt q fE fF hcompatE hcompatF hfE hfF
  let gEout : ↥(↑Eimg : Set P) →
      FreeAmalgam.Vertex Gov TEs TFs tE tF := jE ∘ gE0
  let gFout : ↥(↑Fimg : Set P) →
      FreeAmalgam.Vertex Gov TEs TFs tE tF := jF ∘ gF0
  have ctrlEout :
      ProjectedIntersectionControl
        (Control := Control) (D := D) Eimg Target gEout := by
    intro β
    obtain ⟨βT, hβT, βhit, hβhit⟩ := ctrlE β
    refine ⟨jE.comp βT, ?_, ?_⟩
    · intro a ha
      obtain ⟨a', ha'⟩ := hβT a ha
      exact ⟨a', congrArg jE ha'⟩
    · refine ⟨jE.comp βhit, ?_⟩
      intro x
      exact congrArg jE (hβhit x)
  have ctrlFout :
      ProjectedIntersectionControl
        (Control := Control) (D := D) Fimg Target gFout := by
    intro β
    obtain ⟨βT, hβT, βhit, hβhit⟩ := ctrlF β
    refine ⟨jF.comp βT, ?_, ?_⟩
    · intro a ha
      obtain ⟨a', ha'⟩ := hβT a ha
      exact ⟨a', congrArg jF ha'⟩
    · refine ⟨jF.comp βhit, ?_⟩
      intro x
      exact congrArg jF (hβhit x)
  refine ⟨_, Target, hTree, fOut, hfOut, Eimg, Fimg,
    gEout, gFout, ctrlEout, ctrlFout, ?_, ?_⟩
  · intro e
    change fOut (iE e) = jE (gE0 (pEsub e))
    exact IsFreeAmalgam.liftMap_left
      hSrc hTgt q fE fF hcompatE hcompatF e
  · intro e
    change fOut (iF e) = jF (gF0 (pFsub e))
    exact IsFreeAmalgam.liftMap_right
      hSrc hTgt q fE fF hcompatE hcompatF e

end StructuralRamsey.RelStructure.LocallyTreeLike
