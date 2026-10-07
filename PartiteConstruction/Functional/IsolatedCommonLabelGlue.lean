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


/-- Common isolated A-labels preserve both source-side diary predicates and
control of every ambient copy of the irreducible control structure.  This is
the combined witness needed by the functional mixed Picture induction. -/
theorem glueControlledIsolatedCommonLabels_withSourceHistory
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
    (ctrlE : ∀ α : Embedding Control Esrc,
      ∃ α' : Embedding Control ETgt,
        ∀ a : UA, ∃ a' : UA, hE (α a) = α' a')
    (ctrlF : ∀ α : Embedding Control Fsrc,
      ∃ α' : Embedding Control FTgt,
        ∀ a : UA, ∃ a' : UA, hF (α a) = α' a')
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
        (∀ Hset ∈ history, ∀ x y : C,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) ∧
        ∀ α : Embedding Control Csrc,
          ∃ α' : Embedding Control Target,
            ∀ a : UA, ∃ a' : UA, f (α a) = α' a' := by
  classical
  let Target :=
    FreeAmalgam.amalgam Control ETgt FTgt targetE targetF
  let jE :=
    FreeAmalgam.leftEmbedding Control ETgt FTgt targetE targetF
  let jF :=
    FreeAmalgam.rightEmbedding Control ETgt FTgt targetE targetF
  have hcE : targetE.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetE, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcF : targetF.ContainedInIrreducible := by
    refine ⟨UA, Control, hControl, targetF, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex Control ETgt FTgt targetE targetF) Target :=
    FreeAmalgam.treeAmalgam Control ETgt FTgt targetE targetF Base
      hTreeE hTreeF hcE hcF
  have hTgt :
      IsFreeAmalgam targetE targetF jE jF :=
    FreeAmalgam.isFreeAmalgam Control ETgt FTgt targetE targetF
  let f : C → FreeAmalgam.Vertex Control ETgt FTgt targetE targetF :=
    IsFreeAmalgam.functionalLiftMap hSrc hTgt q hE hF
      hcompatE hcompatF
  have hf : Csrc.IsHomomorphismEmbedding Target f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q hE hF hcompatE hcompatF
      hhE hhF hrootE hrootF
  have hHist :
      ∀ Hset ∈ history, ∀ x y : C,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) :=
    IsFreeAmalgam.functionalLiftMap_respectsSourceSets
      hSrc hTgt q hq hE hF hcompatE hcompatF
      hrootE hrootF history hHistE hHistF
  refine ⟨_, Target, hTree, f, hf, hHist, ?_⟩
  intro α
  rcases hControl hSrc α with hleft | hright
  · let αE : Embedding Control Esrc :=
      α.factorThroughRange iE hleft
    obtain ⟨αT, hαT⟩ := ctrlE αE
    let α' : Embedding Control Target := jE.comp αT
    refine ⟨α', ?_⟩
    intro a
    obtain ⟨a', ha'⟩ := hαT a
    refine ⟨a', ?_⟩
    have hea := Classical.choose_spec (hleft a)
    change f (α a) = jE (αT a')
    calc
      f (α a) = f (iE (αE a)) := congrArg f hea
      _ = jE (hE (αE a)) :=
        IsFreeAmalgam.functionalLiftMap_left
          hSrc hTgt q hE hF hcompatE hcompatF (αE a)
      _ = jE (αT a') := congrArg jE ha'
  · let αF : Embedding Control Fsrc :=
      α.factorThroughRange iF hright
    obtain ⟨αT, hαT⟩ := ctrlF αF
    let α' : Embedding Control Target := jF.comp αT
    refine ⟨α', ?_⟩
    intro a
    obtain ⟨a', ha'⟩ := hαT a
    refine ⟨a', ?_⟩
    have hea := Classical.choose_spec (hright a)
    change f (α a) = jF (αT a')
    calc
      f (α a) = f (iF (αF a)) := congrArg f hea
      _ = jF (hF (αF a)) :=
        IsFreeAmalgam.functionalLiftMap_right
          hSrc hTgt q hE hF hcompatE hcompatF (αF a)
      _ = jF (αT a') := congrArg jF ha'


end StructuralRamsey.Structure.LocallyClosedTreeCompletable
