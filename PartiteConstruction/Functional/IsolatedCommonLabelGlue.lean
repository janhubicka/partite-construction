import PartiteConstruction.Functional.ProjectedPartialEmbedded

/-! # Functional mixed gluing from isolated common A-labels

The relational common-label glue identifies two whole target copies of the
irreducible control A.  For set-valued functions that is sound only when those
copies are isolated: a side point landing anywhere in the target A-copy must
already come from the source overlap, with the same A-label.  Relative
functional history witnesses provide exactly this extra certificate.
-/

namespace StructuralRamsey.Structure.LocallyClosedTreeCompletable

universe u v

variable {L : Language.{u}}
variable {UA VB H E F C TE TF : Type v}
variable {Control : Structure L UA} {Base : Structure L VB}
variable {Dsrc : Structure L H} {Esrc : Structure L E}
variable {Fsrc : Structure L F} {Csrc : Structure L C}
variable {ETgt : Structure L TE} {FTgt : Structure L TF}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Two controlled functional side witnesses with one common injective
A-labelling can be glued over their whole target A-copies, provided both
target copies are root-isolated from the rest of the corresponding side
witness. -/
theorem glueControlled_of_isolatedCommonLabels
    (hControl : Control.Irreducible)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hTreeE : TreeAmalgam Base TE ETgt)
    (hTreeF : TreeAmalgam Base TF FTgt)
    (targetE : Embedding Control ETgt)
    (targetF : Embedding Control FTgt)
    (q : H → UA)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = targetE (q d))
    (hcompatF : ∀ d, hF (sF d) = targetF (q d))
    (hhE : Esrc.IsHomomorphismEmbedding ETgt hE)
    (hhF : Fsrc.IsHomomorphismEmbedding FTgt hF)
    (hrootE : IsFreeAmalgam.RootIsolated sE targetE q hE)
    (hrootF : IsFreeAmalgam.RootIsolated sF targetF q hF)
    (ctrlE : ∀ α : Embedding Control Esrc,
      ∃ α' : Embedding Control ETgt,
        ∀ a : UA, ∃ a' : UA, hE (α a) = α' a')
    (ctrlF : ∀ α : Embedding Control Fsrc,
      ∃ α' : Embedding Control FTgt,
        ∀ a : UA, ∃ a' : UA, hF (α a) = α' a') :
    ∃ (T : Type v) (Target : Structure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ α : Embedding Control Csrc,
          ∃ α' : Embedding Control Target,
            ∀ a : UA, ∃ a' : UA, f (α a) = α' a' := by
  have hcE : targetE.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetE, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcF : targetF.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetF, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  exact glueControlledIsolatedRoot
    (Base := Base) (Control := Control)
    hControl hSrc hTreeE hTreeF hcE hcF q
    hE hF hcompatE hcompatF hhE hhF hrootE hrootF ctrlE ctrlF

/-- Common isolated A-labels also preserve arbitrary source-side diary sets
when the label map is injective. -/
theorem glueIsolatedCommonLabels_withSourceHistory
    (hControl : Control.Irreducible)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (hTreeE : TreeAmalgam Base TE ETgt)
    (hTreeF : TreeAmalgam Base TF FTgt)
    (targetE : Embedding Control ETgt)
    (targetF : Embedding Control FTgt)
    (q : H → UA) (hq : Function.Injective q)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = targetE (q d))
    (hcompatF : ∀ d, hF (sF d) = targetF (q d))
    (hhE : Esrc.IsHomomorphismEmbedding ETgt hE)
    (hhF : Fsrc.IsHomomorphismEmbedding FTgt hF)
    (hrootE : IsFreeAmalgam.RootIsolated sE targetE q hE)
    (hrootF : IsFreeAmalgam.RootIsolated sF targetF q hF)
    (history : List (Set C))
    (hHistE :
      ∀ Hset ∈ history, ∀ x y : E,
        hE x = hE y → (iE x ∈ Hset ↔ iE y ∈ Hset))
    (hHistF :
      ∀ Hset ∈ history, ∀ x y : F,
        hF x = hF y → (iF x ∈ Hset ↔ iF y ∈ Hset)) :
    ∃ (T : Type v) (Target : Structure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ Hset ∈ history, ∀ x y : C,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset) := by
  have hcE : targetE.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetE, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcF : targetF.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetF, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  exact glueIsolatedRoot_withSourceHistory
    (Base := Base)
    hSrc hTreeE hTreeF hcE hcF q hq
    hE hF hcompatE hcompatF hhE hhF
    hrootE hrootF history hHistE hHistF

end StructuralRamsey.Structure.LocallyClosedTreeCompletable
