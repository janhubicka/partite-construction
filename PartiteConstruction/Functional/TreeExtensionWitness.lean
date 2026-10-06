import PartiteConstruction.Functional.TreeExtensionGlue

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

end StructuralRamsey.Structure
