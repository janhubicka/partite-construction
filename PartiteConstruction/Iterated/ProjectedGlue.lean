import PartiteConstruction.Iterated.WitnessGlue

/-! # Gluing local-tree witnesses through the base projection

This is the corrected form of the mixed E/F step from Appendix A.  The two
side witnesses are first built on their projected images in the base D.
The common source overlap may differ from the projected overlap; the projection
map relates them.  Hereditary irreducibility of A makes the projected overlap
irreducible, so the side homomorphism-embeddings restrict there to genuine
embeddings and the two tree witnesses can be freely amalgamated.
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

/-- Glue two finite sides using local-tree witnesses for their projected
images in D. -/
theorem glueProjectedFull
    [Finite E] [Finite F]
    (hControl : HereditarilyIrreducible Control)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (p : C → P) (hp : Csrc.IsHomomorphismEmbedding D p)
    (α : Embedding Control D)
    (hOverlap : ∀ d : H, ∃ a : UA, p (iE (sE d)) = α a)
    (m : ℕ) (hD : LocallyTreeLike Control Base D m)
    (hEcard : ((Finset.univ : Finset E).image (p ∘ iE)).card ≤ m)
    (hFcard : ((Finset.univ : Finset F).image (p ∘ iF)).card ≤ m) :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ γ : Embedding Control Csrc,
          ∃ γ' : Embedding Control Target,
            ∀ a : UA, ∃ a' : UA, f (γ a) = γ' a' := by
  classical
  let pE : E → P := p ∘ iE
  let pF : F → P := p ∘ iF
  have hpE : Esrc.IsHomomorphismEmbedding D pE :=
    hp.comp iE.isHomomorphismEmbedding
  have hpF : Fsrc.IsHomomorphismEmbedding D pF :=
    hp.comp iF.isHomomorphismEmbedding
  obtain ⟨TE, TEs, hTreeE, gE, hgE, ctrlDE, fE, hfE, hfEeq, ctrlE⟩ :=
    projectedWitnessFull
      (A := Control) (B := Base) (C := Esrc)
      hControl.irreducible hD pE hpE hEcard
  obtain ⟨TF, TFs, hTreeF, gF, hgF, ctrlDF, fF, hfF, hfFeq, ctrlF⟩ :=
    projectedWitnessFull
      (A := Control) (B := Base) (C := Fsrc)
      hControl.irreducible hD pF hpF hFcard

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
  have hGov : Gov.Irreducible :=
    hControl.of_embedding eGA

  let Eimg : Finset P := (Finset.univ : Finset E).image pE
  let Fimg : Finset P := (Finset.univ : Finset F).image pF
  let incGE : Embedding Gov (D.induce (↑Eimg : Set P)) := {
    toFun := fun z => ⟨z.1, by
      rcases z.2 with ⟨d, rfl⟩
      exact Finset.mem_image.mpr ⟨sE d, Finset.mem_univ _, rfl⟩⟩
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

  obtain ⟨tE, htE⟩ :=
    hgE.after_irreducible_embedding hGov incGE
  obtain ⟨tF, htF⟩ :=
    hgF.after_irreducible_embedding hGov incGF

  let q : H → Gset := fun d => ⟨q0 d, ⟨d, rfl⟩⟩
  have hcompatE : ∀ d, fE (sE d) = tE (q d) := by
    intro d
    rw [hfEeq (sE d), htE (q d)]
    apply congrArg gE
    apply Subtype.ext
    rfl
  have hcompatF : ∀ d, fF (sF d) = tF (q d) := by
    intro d
    rw [hfFeq (sF d), htF (q d)]
    apply congrArg gF
    apply Subtype.ext
    exact (hqF d).symm

  exact glueControlled
    hControl.irreducible hSrc hGov hTreeE hTreeF
    q fE fF hcompatE hcompatF hfE hfF ctrlE ctrlF

end StructuralRamsey.RelStructure.LocallyTreeLike
