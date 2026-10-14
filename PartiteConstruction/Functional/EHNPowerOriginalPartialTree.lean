import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.WeakInvariant

/-!
# Genuine native Hales–Jewett cores have strict one-copy B-completions

Only the ITERATED functional construction is at issue here. The
function-valued partite power and its EHN projection are already
validated. We do not repeat the recursive or induced Ramsey proof.

For a weakly A-partite genuine function-valued core, the whole
positive power EHN-maps to A. Composing with A ↪ Base supplies an
original-2019 partial homomorphism-embedding directly into Base.
Consequently even the ENTIRE power has a strict one-copy Base-tree
completion, without requiring reflection of undefined function domains.

This discharges the pure-core branch of the proposed strict functional
Picture induction. It does not discharge the mixed attachment branch,
where a reducible common separator needs synchronized relative
extensions.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V VB : Type v}

/-- A genuinely functional Hales–Jewett power has a strict full
functional Base-tree target under the ORIGINAL partial-homomorphism
convention, provided the selected control A fully embeds in Base. -/
theorem power_hasOriginalPartialTreeCompletion
    (A : Structure L P)
    (R : System L P V)
    (hR : R.WeaklyPartiteOver A)
    (Base : Structure L VB)
    (eAB : Embedding A Base)
    (N : ℕ) (hN : 0 < N) :
    HasOriginalPartialTreeCompletion Base (power R N).toStructure := by
  have hPower :
      (power R N).toStructure.IsEHNHomomorphismEmbedding
        A (power R N).part :=
    power_weaklyPartiteOver hR hN
  have hTarget :
      (power R N).toStructure.IsEHNHomomorphismEmbedding Base
        (eAB ∘ (power R N).part) :=
    eAB.isEHNHomomorphismEmbedding.comp hPower
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    Base (power R N).toStructure (eAB ∘ (power R N).part) hTarget

end StructuralRamsey.FunctionalPartite.Induced
