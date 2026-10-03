import PartiteConstruction.Iterated.WitnessGlue

/-! # The mixed-overlap kernel obstruction

The mixed E/F proof cannot glue arbitrary local witnesses when the common
projected overlap is reducible. Compatibility through a common target
overlap forces the two side maps to have exactly the same equality kernel on
the source overlap.

Thus, if one homomorphism-embedding collapses two overlap vertices and the
other separates them, no choice of target overlap and target embeddings can
repair the mismatch. Hereditary irreducibility prevents this by making both
restrictions embeddings. Any proof under mere irreducibility must instead
construct side witnesses with compatible kernels (or carry stronger
restriction-compatible witness data).
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {H E F G TE TF : Type v}
variable {Dsrc : RelStructure L H}
variable {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F}
variable {Gov : RelStructure L G}
variable {ETgt : RelStructure L TE}
variable {FTgt : RelStructure L TF}
variable {sE : Embedding Dsrc Esrc}
variable {sF : Embedding Dsrc Fsrc}
variable {tE : Embedding Gov ETgt}
variable {tF : Embedding Gov FTgt}

/-- Factoring two side maps through embeddings of one common target overlap
forces equality of their kernels on the source overlap. -/
theorem compatible_overlap_kernel_iff
    (q : H → G) (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = tE (q d))
    (hcompatF : ∀ d, hF (sF d) = tF (q d))
    (x y : H) :
    hE (sE x) = hE (sE y) ↔ hF (sF x) = hF (sF y) := by
  constructor
  · intro hxy
    have hq : q x = q y := by
      apply tE.injective
      rw [← hcompatE x, ← hcompatE y]
      exact hxy
    rw [hcompatF x, hcompatF y, hq]
  · intro hxy
    have hq : q x = q y := by
      apply tF.injective
      rw [← hcompatF x, ← hcompatF y]
      exact hxy
    rw [hcompatE x, hcompatE y, hq]

/-- A concrete mismatched-kernel pair cannot be made compatible through any
common target overlap embedded on both sides. -/
theorem no_compatible_overlap_of_kernel_mismatch
    (hE : E → TE) (hF : F → TF)
    (x y : H)
    (hcollapse : hE (sE x) = hE (sE y))
    (hseparate : hF (sF x) ≠ hF (sF y)) :
    ¬ ∃ (G : Type v) (Gov : RelStructure L G)
        (tE : Embedding Gov ETgt) (tF : Embedding Gov FTgt)
        (q : H → G),
        (∀ d, hE (sE d) = tE (q d)) ∧
        (∀ d, hF (sF d) = tF (q d)) := by
  rintro ⟨G, Gov, tE', tF', q, hcompatE, hcompatF⟩
  have h :
      hE (sE x) = hE (sE y) ↔ hF (sF x) = hF (sF y) :=
    compatible_overlap_kernel_iff
      (Dsrc := Dsrc) (Esrc := Esrc) (Fsrc := Fsrc)
      (Gov := Gov) (ETgt := ETgt) (FTgt := FTgt)
      (sE := sE) (sF := sF) (tE := tE') (tF := tF')
      q hE hF hcompatE hcompatF x y
  exact hseparate (h.mp hcollapse)

/-- Necessary condition for the current controlled-gluing interface:
restrictions of the two side maps to the source overlap must have the same
kernel. -/
theorem same_kernel_of_controlled_gluing_data
    (q : H → G) (hE : E → TE) (hF : F → TF)
    (hcompatE : ∀ d, hE (sE d) = tE (q d))
    (hcompatF : ∀ d, hF (sF d) = tF (q d)) :
    ∀ x y : H,
      hE (sE x) = hE (sE y) ↔ hF (sF x) = hF (sF y) :=
  fun x y =>
    compatible_overlap_kernel_iff
      q hE hF hcompatE hcompatF x y

end StructuralRamsey.RelStructure.LocallyTreeLike
