import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.WeakInvariant

/-!
# The genuine functional Hales--Jewett core needs no strict-tree induction

The native iterated partite construction uses the actual set-valued-function
Hales--Jewett power, not an intermediate U-closed relational structure.

Its EHN projection into the selected A, followed by the full embedding
A ↪ Base, is an original-2019 partial homomorphism-embedding to Base.
Therefore the WHOLE core admits a one-copy strict full-functional
Base-tree completion, with no rank bound.

Moreover any genuine function-closed substructure of the core admits
the same one-copy completion. This is not asserted for arbitrary weak
substructures, which can omit a function output and be irreducible.

Thus, for the strict original-partial n-pass induction, the core is
settled. The genuinely mixed closed attachment over a reducible
separator remains the only local geometry not supplied here.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {P V VB : Type v}

/-- Every genuine native Hales--Jewett power of an EHN A-partite
system has a strict original-partial completion inside a SINGLE Base
copy whenever A fully embeds in Base. No finiteness, n-rank or closure
description is needed for this whole-core statement. -/
theorem nativePower_originalPartial_oneCopy
    (A : Structure L P)
    (Base : Structure L VB)
    (R : System L P V)
    (hR : R.WeaklyPartiteOver A)
    (eAB : Embedding A Base)
    (N : ℕ) (hN : 0 < N) :
    HasOriginalPartialTreeCompletion Base
      (Induced.power R N).toStructure := by
  let E := Induced.power R N
  have hE : E.WeaklyPartiteOver A :=
    Induced.power_weaklyPartiteOver hR hN
  have hp : E.toStructure.IsEHNHomomorphismEmbedding
      Base (eAB ∘ E.part) :=
    eAB.isEHNHomomorphismEmbedding.comp hE
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    Base E.toStructure (eAB ∘ E.part) hp

/-- Every FULL function-closed test inside the genuine power core
also completes inside a single Base-copy by restricting the SAME
original-partial EHN projection. The source vertex set is unchanged. -/
theorem nativePower_closedTest_originalPartial_oneCopy
    (A : Structure L P)
    (Base : Structure L VB)
    (R : System L P V)
    (hR : R.WeaklyPartiteOver A)
    (eAB : Embedding A Base)
    (N : ℕ) (hN : 0 < N)
    (S : Set (Induced.Vertex R N))
    (hS : (Induced.power R N).toStructure.IsClosed S) :
    HasOriginalPartialTreeCompletion Base
      ((Induced.power R N).toStructure.induce S hS) := by
  let E := Induced.power R N
  have hE : E.WeaklyPartiteOver A :=
    Induced.power_weaklyPartiteOver hR hN
  let incl : Embedding (E.toStructure.induce S hS) E.toStructure :=
    inclusion E.toStructure S hS
  have hp : (E.toStructure.induce S hS).IsEHNHomomorphismEmbedding
      Base ((eAB ∘ E.part) ∘ incl) :=
    (eAB.isEHNHomomorphismEmbedding.comp hE).comp
      incl.isEHNHomomorphismEmbedding
  exact HasOriginalPartialTreeCompletion.ofEHN_to_base
    Base (E.toStructure.induce S hS)
      ((eAB ∘ E.part) ∘ incl) hp

end StructuralRamsey.FunctionalPartite.EHN
