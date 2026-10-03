import PartiteConstruction.Iterated.FinalAttachment

/-! # Reconstructing a root embedding into the base

The final sparsening projection says that the projected image of an
irreducible root lies in some copy of the base.  Since a
homomorphism-embedding is induced on an irreducible root, the root itself
therefore embeds into that base copy.  This file packages that reconstruction
without actually performing an attachment.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H X VB Y : Type v}
variable {Root : RelStructure L H}
variable {Core : RelStructure L X}
variable {Base : RelStructure L VB}
variable {Q : RelStructure L Y}

/-- Reconstruct the root embedding into Base from its projected containment
in a Base-copy of Q. -/
theorem rootEmbeddingIntoBase
    (hRoot : Root.Irreducible)
    (fCore : Embedding Root Core)
    (pCore : X → Y)
    (hpCore : Core.IsHomomorphismEmbedding Q pCore)
    (β : Embedding Base Q)
    (hcover : ∀ d : H, ∃ b : VB, pCore (fCore d) = β b) :
    ∃ fBase : Embedding Root Base,
      ∀ d : H, pCore (fCore d) = β (fBase d) := by
  obtain ⟨eRootQ, heRootQ⟩ :=
    hpCore.after_irreducible_embedding hRoot fCore
  have hrange : ∀ d : H, ∃ b : VB, eRootQ d = β b := by
    intro d
    obtain ⟨b, hb⟩ := hcover d
    exact ⟨b, (heRootQ d).trans hb⟩
  let fBase : Embedding Root Base :=
    eRootQ.factorThroughRange β hrange
  refine ⟨fBase, ?_⟩
  intro d
  calc
    pCore (fCore d) = eRootQ d := (heRootQ d).symm
    _ = β (fBase d) := by
      change eRootQ d = β (Classical.choose (hrange d))
      exact Classical.choose_spec (hrange d)

end StructuralRamsey.RelStructure
