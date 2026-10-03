import PartiteConstruction.Functional.FunctionDomains
import PartiteConstruction.Functional.SingletonPartite

/-! # Semi-closed invariants through partite operations

For the domain-expanded partial-function language, semi-closedness consists of
two independent facts:
* every output tuple carries its domain/root tuple;
* outputs are unique for a fixed input tuple.

The second fact is handled in `SingletonPartite`.  This file tracks the
first one through the operations used by the recursive partite construction.
-/
namespace StructuralRamsey.Partite

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P Q V W X : Type v}

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
  have hyA :
      A.rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x y) := hy
  have hout :
      A.rel (.inr F)
        (Structure.funcTuple (Subtype.val ∘ x) y.1) := by
    have ht :
        Subtype.val ∘ Structure.funcTuple x y =
          Structure.funcTuple (Subtype.val ∘ x) y.1 :=
      Structure.comp_funcTuple Subtype.val x y
    exact Eq.mp
      (congrArg (fun t => A.rel (.inr F) t) ht)
      hyA
  have hdom :
      A.rel (.inl (.inr F)) (Subtype.val ∘ x) :=
    h F (Subtype.val ∘ x) y.1 hout
  exact hdom

/-- Restriction to selected parts preserves output-to-domain compatibility. -/
theorem System.restrict_outputImpliesDomain
    {A : System L.withFunctionDomains.graph P V}
    (α : Q ↪ P)
    (h : A.OutputImpliesDomain) :
    (A.restrict α).OutputImpliesDomain :=
  System.induce_outputImpliesDomain h

/-- Relabelling parts changes no relations. -/
theorem System.relabel_outputImpliesDomain
    {A : System L.withFunctionDomains.graph P V}
    (α : P ↪ Q)
    (h : A.OutputImpliesDomain) :
    (A.relabel α).OutputImpliesDomain :=
  h

namespace Closed.Induced

/-- Coordinate powers preserve output-to-domain compatibility. -/
theorem power_outputImpliesDomain
    {A : RelStructure L.withFunctionDomains.graph P}
    {B : System L.withFunctionDomains.graph P V}
    {N : ℕ}
    (hB : B.OutputImpliesDomain) :
    (Partite.Induced.power B N).OutputImpliesDomain := by
  intro F x y hy
  intro k
  have hyk :
      B.rel (.inr F)
        (fun j =>
          (Structure.funcTuple x y j).coord k) :=
    hy k
  let args : Fin (L.funcArity F) → V :=
    fun i => (x i).coord k
  have ht :
      (fun j =>
        (Structure.funcTuple x y j).coord k) =
        Structure.funcTuple args (y.coord k) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [args, Structure.funcTuple]
    · simp [args, Structure.funcTuple]
  have hout :
      B.rel (.inr F)
        (Structure.funcTuple args (y.coord k)) := by
    rw [← ht]
    exact hyk
  exact hB F args (y.coord k) hout

end Closed.Induced

namespace HalfClosed.Initial

/-- The ordinary-indexed initial picture preserves output-to-domain
compatibility. -/
theorem outputImpliesDomain
    (B : RelStructure L.withFunctionDomains.graph V)
    (D : RelStructure L.withFunctionDomains.graph P)
    (hB : B.OutputImpliesDomain) :
    (picture B D).OutputImpliesDomain := by
  intro F x y hy
  rcases hy with ⟨i, q, hq, heq⟩
  let args : Fin (L.funcArity F) → V :=
    fun k => q (Fin.castSucc k)
  let out : V := q (Fin.last (L.funcArity F))
  have hqout :
      B.rel (.inr F) (Structure.funcTuple args out) := by
    have heta : Structure.funcTuple args out = q := by
      simpa [args, out, Language.graph] using
        (Structure.funcTuple_eta (t := q))
    rw [heta]
    exact hq
  have hroot : B.rel (.inl (.inr F)) args :=
    hB F args out hqout
  refine ⟨i, args, hroot, ?_⟩
  funext k
  have hk := congrFun heq (Fin.castSucc k)
  rw [Structure.funcTuple_castSucc] at hk
  exact hk

end HalfClosed.Initial

namespace Attachment

/-- Ordinary free attachment preserves the implication output -> domain/root.
It may destroy uniqueness of the output, which is precisely why the
intermediate little picture need not be semi-closed. -/
theorem outputImpliesDomain
    {I : Type v}
    {B : Partite.System L.withFunctionDomains.graph P V}
    {S : Set V}
    {D : Partite.System L.withFunctionDomains.graph P W}
    {f : I → Partite.Embedding (B.induce S) D}
    (hB : B.OutputImpliesDomain)
    (hD : D.OutputImpliesDomain) :
    (Partite.Attachment.attach B S D f).OutputImpliesDomain := by
  classical
  intro F x y hy
  rcases hy with ⟨q, hq, hcore⟩ | ⟨i, q, hq, hcopy⟩
  · let args : Fin (L.funcArity F) → W :=
      fun k => q (Fin.castSucc k)
    let out : W := q (Fin.last (L.funcArity F))
    have hout :
        D.rel (.inr F) (Structure.funcTuple args out) := by
      have heta : Structure.funcTuple args out = q := by
        simpa [args, out, Language.graph] using
          (Structure.funcTuple_eta (t := q))
      rw [heta]
      exact hq
    have hroot := hD F args out hout
    refine Or.inl ⟨args, hroot, ?_⟩
    funext k
    have hk := congrFun hcore (Fin.castSucc k)
    rw [Structure.funcTuple_castSucc] at hk
    exact hk
  · let args : Fin (L.funcArity F) → V :=
      fun k => q (Fin.castSucc k)
    let out : V := q (Fin.last (L.funcArity F))
    have hout :
        B.rel (.inr F) (Structure.funcTuple args out) := by
      have heta : Structure.funcTuple args out = q := by
        simpa [args, out, Language.graph] using
          (Structure.funcTuple_eta (t := q))
      rw [heta]
      exact hq
    have hroot := hB F args out hout
    refine Or.inr ⟨i, args, hroot, ?_⟩
    funext k
    have hk := congrFun hcopy (Fin.castSucc k)
    rw [Structure.funcTuple_castSucc] at hk
    exact hk

end Attachment

namespace Nested

/-- Flattening changes only the part map. -/
theorem flatten_outputImpliesDomain
    (O : Partite.System L.withFunctionDomains.graph P W)
    (C : Partite.System L.withFunctionDomains.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure)
    (h : C.OutputImpliesDomain) :
    (flatten O C hC).OutputImpliesDomain :=
  h

end Nested

/-- Adding unary part predicates preserves output-to-domain compatibility. -/
theorem outputImpliesDomain_expandFunctional
    {A : Partite.System L.withFunctionDomains.graph P V}
    (h : A.OutputImpliesDomain) :
    A.expandFunctional.OutputImpliesDomain := by
  intro F x y hy
  have hroot := h F.down x y hy
  exact hroot

/-- Forgetting unary part predicates preserves output-to-domain
compatibility. -/
theorem outputImpliesDomain_ofFunctionalExpansion
    {C : Partite.System
      (L.withFunctionDomains.withParts P).graph Q V}
    (h : C.toRelStructure.OutputImpliesDomain) :
    (C.ofFunctionalExpansion).OutputImpliesDomain := by
  intro F x y hy
  have hroot := h (ULift.up F) x y hy
  exact hroot

end StructuralRamsey.Partite
