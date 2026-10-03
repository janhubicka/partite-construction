import PartiteConstruction.Iterated.RelativeLabelledLocalTreeLike

/-! # Mixed projected gluing from relative labelled completions

This is the positive mixed E/F theorem corresponding to the relative-labelled
invariant.  The projected construction overlap lies inside one distinguished
copy alpha : A -> D.  Let q : Hsrc -> A record its unique A-labels.

Complete each projected side using the relative invariant with the same alpha
and the same label subset range(q).  The two witnesses therefore agree with
their target A-copies at exactly the labels q(d) on every overlap point d.
The checked common-label gluing theorem then applies directly.

Only irreducibility of A is used.
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

/-- Glue the two projected sides when D supplies relative labelled
completions. -/
theorem glueProjectedFull_relativeLabelled
    [Fintype E] [Fintype F] [DecidableEq P]
    (hControl : Control.Irreducible)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (p : C → P) (hp : Csrc.IsHomomorphismEmbedding D p)
    (α : Embedding Control D)
    (hOverlap : ∀ d : H, ∃ a : UA, p (iE (sE d)) = α a)
    (m : ℕ)
    (hD : RelativeLabelledLocallyTreeLike
      (A := Control) (B := Base) (D := D) m)
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
  let Eimg : Finset P := (Finset.univ : Finset E).image pE
  let Fimg : Finset P := (Finset.univ : Finset F).image pF

  let q0 : H → P := fun d => p (iE (sE d))
  let qA : H → UA := fun d => Classical.choose (hOverlap d)
  have hqA (d : H) : q0 d = α (qA d) :=
    Classical.choose_spec (hOverlap d)
  have hqF (d : H) : q0 d = pF (sF d) := by
    change p (iE (sE d)) = p (iF (sF d))
    apply congrArg p
    exact (hSrc.overlap (sE d) (sF d)).mpr ⟨d, rfl, rfl⟩

  let Hset : Set UA := Set.range qA
  have hHE : ∀ a : Hset, α a.1 ∈ Eimg := by
    intro a
    rcases a.2 with ⟨d, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨sE d, Finset.mem_univ _, ?_⟩
    exact (hqA d).symm
  have hHF : ∀ a : Hset, α a.1 ∈ Fimg := by
    intro a
    rcases a.2 with ⟨d, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨sF d, Finset.mem_univ _, ?_⟩
    calc
      pF (sF d) = q0 d := (hqF d).symm
      _ = α (qA d) := hqA d

  obtain ⟨TE, TEs, hTreeE, gE, hgE, ctrlDE, targetE, htargetE⟩ :=
    hD.2 Eimg hEcard α Hset hHE
  obtain ⟨TF, TFs, hTreeF, gF, hgF, ctrlDF, targetF, htargetF⟩ :=
    hD.2 Fimg hFcard α Hset hHF

  let pEsub : E → ↥(↑Eimg : Set P) :=
    fun e => ⟨pE e,
      Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
  let pFsub : F → ↥(↑Fimg : Set P) :=
    fun e => ⟨pF e,
      Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
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

  let fE : E → TE := gE ∘ pEsub
  let fF : F → TF := gF ∘ pFsub
  have hfE : Esrc.IsHomomorphismEmbedding TEs fE :=
    hgE.comp hpEsub
  have hfF : Fsrc.IsHomomorphismEmbedding TFs fF :=
    hgF.comp hpFsub

  have ctrlE : ∀ γ : Embedding Control Esrc,
      ∃ γ' : Embedding Control TEs,
        ∀ a : UA, ∃ a' : UA, fE (γ a) = γ' a' := by
    intro γ
    obtain ⟨γD, hγD⟩ := hpE.after_irreducible_embedding hControl γ
    obtain ⟨γT, hγT⟩ := ctrlDE γD
    refine ⟨γT, ?_⟩
    intro a
    have ha : γD a ∈ Eimg := by
      apply Finset.mem_image.mpr
      refine ⟨γ a, Finset.mem_univ _, ?_⟩
      exact (hγD a).symm
    obtain ⟨a', ha'⟩ := hγT a ha
    refine ⟨a', ?_⟩
    change gE (pEsub (γ a)) = γT a'
    have heq :
        pEsub (γ a) =
          (⟨γD a, ha⟩ : ↥(↑Eimg : Set P)) := by
      apply Subtype.ext
      exact (hγD a).symm
    rw [heq]
    exact ha'
  have ctrlF : ∀ γ : Embedding Control Fsrc,
      ∃ γ' : Embedding Control TFs,
        ∀ a : UA, ∃ a' : UA, fF (γ a) = γ' a' := by
    intro γ
    obtain ⟨γD, hγD⟩ := hpF.after_irreducible_embedding hControl γ
    obtain ⟨γT, hγT⟩ := ctrlDF γD
    refine ⟨γT, ?_⟩
    intro a
    have ha : γD a ∈ Fimg := by
      apply Finset.mem_image.mpr
      refine ⟨γ a, Finset.mem_univ _, ?_⟩
      exact (hγD a).symm
    obtain ⟨a', ha'⟩ := hγT a ha
    refine ⟨a', ?_⟩
    change gF (pFsub (γ a)) = γT a'
    have heq :
        pFsub (γ a) =
          (⟨γD a, ha⟩ : ↥(↑Fimg : Set P)) := by
      apply Subtype.ext
      exact (hγD a).symm
    rw [heq]
    exact ha'

  have hcompatE : ∀ d, fE (sE d) = targetE (qA d) := by
    intro d
    let aH : Hset := ⟨qA d, ⟨d, rfl⟩⟩
    have hmem : α (qA d) ∈ Eimg := hHE aH
    change gE (pEsub (sE d)) = targetE (qA d)
    have heq :
        pEsub (sE d) =
          (⟨α (qA d), hmem⟩ : ↥(↑Eimg : Set P)) := by
      apply Subtype.ext
      exact (hqA d).symm
    rw [heq]
    exact htargetE aH
  have hcompatF : ∀ d, fF (sF d) = targetF (qA d) := by
    intro d
    let aH : Hset := ⟨qA d, ⟨d, rfl⟩⟩
    have hmem : α (qA d) ∈ Fimg := hHF aH
    change gF (pFsub (sF d)) = targetF (qA d)
    have heq :
        pFsub (sF d) =
          (⟨α (qA d), hmem⟩ : ↥(↑Fimg : Set P)) := by
      apply Subtype.ext
      calc
        pF (sF d) = q0 d := (hqF d).symm
        _ = α (qA d) := hqA d
    rw [heq]
    exact htargetF aH

  exact glueControlled_of_commonLabels
    hControl hSrc hTreeE hTreeF targetE targetF qA
    fE fF hcompatE hcompatF hfE hfF ctrlE ctrlF

end StructuralRamsey.RelStructure.LocallyTreeLike
