import PartiteConstruction.Functional.FunctionDomains
import PartiteConstruction.Functional.SingletonPartite

/-! # Semi-closed invariants needed by the recursive little picture

The intermediate little picture is not required to be U-transversal.  The
recursive proof only needs the relevant overlap to retain the outer partite
projection and the root/domain information of partial functions.

This file deliberately records only those local invariants.  Stronger global
preservation statements are unnecessary for the corrected recursive proof.
-/
namespace StructuralRamsey.Partite

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P Q V : Type v}

/-- Inducing on an arbitrary vertex subset preserves the outer
homomorphism-embedding projection. -/
theorem System.induce_isPartiteOver
    {K : RelLanguage.{u}}
    {A : Partite.System K P V}
    {D : RelStructure K P}
    {S : Set V}
    (h : A.IsPartiteOver D) :
    (A.induce S).IsPartiteOver D := by
  change
    (A.toRelStructure.induce S).IsHomomorphismEmbedding D
      (fun x => A.part x.1)
  have hincl :
      (A.toRelStructure.induce S).IsHomomorphismEmbedding
        A.toRelStructure Subtype.val :=
    (A.toRelStructure.inclusion S).isHomomorphismEmbedding
  have hc := h.comp hincl
  simpa [Function.comp_def] using hc

abbrev System.OutputImpliesDomain
    (A : System L.withFunctionDomains.graph P V) : Prop :=
  A.toRelStructure.OutputImpliesDomain

abbrev System.FunctionSemiClosed
    (A : System L.withFunctionDomains.graph P V) : Prop :=
  A.toRelStructure.FunctionSemiClosed

theorem System.semiClosed_iff
    {A : System L.withFunctionDomains.graph P V} :
    A.FunctionSemiClosed ↔
      A.OutputImpliesDomain ∧
      A.FunctionOutputSingleValued :=
  Iff.rfl

/-- Induced subsystems preserve output-to-domain compatibility. -/
theorem System.induce_outputImpliesDomain
    {A : System L.withFunctionDomains.graph P V}
    {S : Set V}
    (h : A.OutputImpliesDomain) :
    (A.induce S).OutputImpliesDomain := by
  intro F x y hy
  have hy0 :
      A.rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x y) := hy
  have ht :
      Subtype.val ∘ Structure.funcTuple x y =
        Structure.funcTuple (Subtype.val ∘ x) y.1 :=
    Structure.comp_funcTuple Subtype.val x y
  have hyA :
      A.rel (.inr F)
        (Structure.funcTuple (Subtype.val ∘ x) y.1) :=
    Eq.mp
      (congrArg (fun t => A.rel (.inr F) t) ht)
      hy0
  have hdom :
      A.rel (.inl (.inr F)) (Subtype.val ∘ x) :=
    h F (Subtype.val ∘ x) y.1 hyA
  exact hdom

/-- Restriction to selected parts preserves output-to-domain compatibility. -/
theorem System.restrict_outputImpliesDomain
    {A : System L.withFunctionDomains.graph P V}
    (α : Q ↪ P)
    (h : A.OutputImpliesDomain) :
    (A.restrict α).OutputImpliesDomain :=
  System.induce_outputImpliesDomain h

end StructuralRamsey.Partite
