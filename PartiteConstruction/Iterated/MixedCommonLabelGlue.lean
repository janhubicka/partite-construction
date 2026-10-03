import PartiteConstruction.Iterated.WitnessGlue
import PartiteConstruction.Iterated.LabelledIntersectionControl

/-! # Mixed gluing from one common A-labelling

The remaining mixed E/F issue can be phrased without mentioning reducible
target overlaps at all.  If both side witnesses send the source overlap into
controlled copies of A with the *same* label map q : H -> A, then glue the
two target trees over the entire target A-copies.

Because A itself is irreducible, this is an allowed tree-amalgam gluing and
the existing controlled lift immediately gives a homomorphism-embedding of
the source free amalgam.  No hereditary irreducibility of A is used.

Thus the missing existence statement in the survey proof is exactly the
ability to choose the two side completions with a common A-labelling on their
reducible overlap.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB H E F C TE TF : Type v}
variable {Control : RelStructure L UA} {Base : RelStructure L VB}
variable {Dsrc : RelStructure L H} {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F} {Csrc : RelStructure L C}
variable {ETgt : RelStructure L TE} {FTgt : RelStructure L TF}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Two controlled side witnesses with one common label map into A can be
glued over their whole target A-copies. -/
theorem glueControlled_of_commonLabels
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
    (ctrlE : ∀ α : Embedding Control Esrc,
      ∃ α' : Embedding Control ETgt,
        ∀ a : UA, ∃ a' : UA, hE (α a) = α' a')
    (ctrlF : ∀ α : Embedding Control Fsrc,
      ∃ α' : Embedding Control FTgt,
        ∀ a : UA, ∃ a' : UA, hF (α a) = α' a') :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam Base T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ α : Embedding Control Csrc,
          ∃ α' : Embedding Control Target,
            ∀ a : UA, ∃ a' : UA, f (α a) = α' a' := by
  exact glueControlled
    hControl hSrc hControl hTreeE hTreeF
    q hE hF hcompatE hcompatF hhE hhF ctrlE ctrlF

/-- The common-label condition is unchanged after postcomposing each side
target by an embedding. -/
theorem commonLabels_postcomp
    {ZE ZF : Type v}
    {ETgt' : RelStructure L ZE} {FTgt' : RelStructure L ZF}
    (targetE : Embedding Control ETgt)
    (targetF : Embedding Control FTgt)
    (q : H → UA)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = targetE (q d))
    (hcompatF : ∀ d, hF (sF d) = targetF (q d))
    (jE : Embedding ETgt ETgt')
    (jF : Embedding FTgt FTgt') :
    (∀ d, (jE ∘ hE) (sE d) = (jE.comp targetE) (q d)) ∧
    (∀ d, (jF ∘ hF) (sF d) = (jF.comp targetF) (q d)) := by
  constructor
  · intro d
    exact congrArg jE (hcompatE d)
  · intro d
    exact congrArg jF (hcompatF d)

/-- A common label map automatically gives equal kernels on the overlap. -/
theorem sameKernel_of_commonLabels
    (targetE : Embedding Control ETgt)
    (targetF : Embedding Control FTgt)
    (q : H → UA)
    (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = targetE (q d))
    (hcompatF : ∀ d, hF (sF d) = targetF (q d)) :
    ∀ x y : H,
      hE (sE x) = hE (sE y) ↔
      hF (sF x) = hF (sF y) := by
  intro x y
  constructor
  · intro hxy
    have hq : q x = q y := by
      apply targetE.injective
      rw [← hcompatE x, ← hcompatE y]
      exact hxy
    rw [hcompatF x, hcompatF y, hq]
  · intro hxy
    have hq : q x = q y := by
      apply targetF.injective
      rw [← hcompatF x, ← hcompatF y]
      exact hxy
    rw [hcompatE x, hcompatE y, hq]

end StructuralRamsey.RelStructure.LocallyTreeLike
