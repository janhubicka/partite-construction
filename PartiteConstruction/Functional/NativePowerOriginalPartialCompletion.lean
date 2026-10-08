import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.NativePowerTwelveBound

/-! # Reassessing the native-power obstruction under 2019 semantics

The tagged Hales--Jewett power and its closed staircase test fail the
later survey's **full total-fibre** homomorphism-embedding completion
condition. However, their native EHN part maps are homomorphism-embeddings
in the ORIGINAL partial-function convention of 2019.

Thus these examples cannot serve as obstructions to the literal
2019 strict-local-tree conclusion. The targets are still genuine strict
full-function B-trees; only the required *completion map* is weaker.

This file does NOT assert the stronger generic strict local induction
of the 2019 theorem for arbitrary control structures. The particular
staircase has its base as the original projection target.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The original seven-vertex part projection is a 2019-style
partial-function homomorphism-embedding, even though it is not
globally full in the total set-valued-function semantics. -/
theorem oldStage_originalPartialHE :
    IsOriginalPartialHomomorphismEmbedding oldStage toyBase oldPart :=
  oldStage_projection.toOriginalPartial

/-- A concrete undefined input in the source maps to a *defined*
input in the base. Domain reflection is not required of a 2019
homomorphism, and is exactly the extra condition imposed by the
later total-set-valued encoding. -/
theorem oldStage_not_totalFibreHom :
    ¬ oldStage.IsHomomorphism toyBase oldPart := by
  let args : Fin 2 → Fin 7 := ![0,3]
  have hnone : ¬ (oldStage.func () args).Nonempty := by
    rintro ⟨z,hz⟩
    change oldOutput 0 3 = some z at hz
    have hzero : oldOutput 0 3 = none := by decide
    rw [hzero] at hz
    cases hz
  have htgt : (toyBase.func () (oldPart ∘ args)).Nonempty := by
    refine ⟨(2 : Fin 3), ?_⟩
    change oldPart 0 = 0 ∧ oldPart 3 = 1 ∧ (2 : Fin 3) = 2
    decide
  intro hfull
  obtain ⟨z,hz⟩ := htgt
  have himg : z ∈ imageSet oldPart (oldStage.func () args) := by
    rw [hfull.2 () args]
    exact hz
  obtain ⟨v,hv,_⟩ := himg
  exact hnone ⟨v,hv⟩

/-- The full genuine tagged native power has a single-copy STRICT
B-tree completion in the 2019 partial-function meaning. The map is
precisely the checked EHN part projection. -/
theorem actualPower_originalPartialTreeCompletion :
    HasOriginalPartialTreeCompletion toyBase actualPower := by
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    toyBase actualPower
    (FunctionalPartite.Induced.power oldSystem 2).part
    actualPower_weaklyPartiteOver

/-- Even the proper closed 12-vertex staircase support has a
2019-style strict B-tree completion: restrict the native EHN part
map to this genuine closed source substructure. -/
theorem staircase_originalPartialTreeCompletion :
    HasOriginalPartialTreeCompletion toyBase
      (actualPower.induce StaircaseSupport staircaseSupport_closed) := by
  let inc : Embedding
      (actualPower.induce StaircaseSupport staircaseSupport_closed)
      actualPower :=
    inclusion actualPower StaircaseSupport staircaseSupport_closed
  have hp :
      (actualPower.induce StaircaseSupport staircaseSupport_closed).IsEHNHomomorphismEmbedding toyBase
          ((FunctionalPartite.Induced.power oldSystem 2).part ∘ Subtype.val) := by
    change
      (actualPower.induce StaircaseSupport staircaseSupport_closed).IsEHNHomomorphismEmbedding toyBase
          ((FunctionalPartite.Induced.power oldSystem 2).part ∘ inc)
    exact actualPower_weaklyPartiteOver.comp
      inc.isEHNHomomorphismEmbedding
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    toyBase (actualPower.induce StaircaseSupport staircaseSupport_closed)
    ((FunctionalPartite.Induced.power oldSystem 2).part ∘ Subtype.val) hp

/-- **Semantic divergence certified in Lean:** the same proper, closed
native-power test has an original-2019 partial-homomorphism-embedding
strict B-tree completion, but no completion with the later survey's
full fibre equality on *every* tuple.

The latter negative result is still correct under its own stronger
definition; it cannot be used against the original 2019 formulation. -/
theorem staircase_originalPartial_yes_totalFibre_no :
    HasOriginalPartialTreeCompletion toyBase
      (actualPower.induce StaircaseSupport staircaseSupport_closed) ∧
    ¬ HasTreeCompletion toyBase
      (actualPower.induce StaircaseSupport staircaseSupport_closed) :=
  ⟨staircase_originalPartialTreeCompletion,
    staircaseSupport_no_strictTreeCompletion⟩

end StructuralRamsey.Structure.NativePowerObstruction
