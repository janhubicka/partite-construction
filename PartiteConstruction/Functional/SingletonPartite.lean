import PartiteConstruction.Functional.ClosedAttachment
import PartiteConstruction.Functional.HalfClosedInitial
import PartiteConstruction.Functional.NestedFlatten

/-! # Singleton-valued invariants for graph-partite constructions

After the ordered rank reduction, every function symbol is partial:
for a fixed input tuple there is at most one output.  This file records the
corresponding graph invariant and its preservation by the basic constructions.

The invariant is stronger than U-transversality and, unlike
U-transversality, does not depend on the current part map.
-/
namespace StructuralRamsey

open Structure

universe u v
variable {L : Language.{u}}

namespace RelStructure

/-- Every encoded function graph has at most one output over a fixed input. -/
def FunctionOutputSingleValued
    {V : Type v} (A : RelStructure L.graph V) : Prop :=
  ∀ F (x : Fin (L.funcArity F) → V) y z,
    A.rel (.inr F) (funcTuple x y) →
    A.rel (.inr F) (funcTuple x z) →
    y = z

end RelStructure

namespace Partite

variable {P V W X : Type v}

/-- Singleton-valuedness of the relational reduct of a partite system. -/
abbrev System.FunctionOutputSingleValued
    (A : System L.graph P V) : Prop :=
  A.toRelStructure.FunctionOutputSingleValued

/-- Singleton-valuedness immediately implies U-transversality for every
partition map. -/
theorem System.FunctionOutputSingleValued.uTransversal
    {A : System L.graph P V}
    (h : A.FunctionOutputSingleValued) :
    A.FunctionOutputTransversal := by
  intro F x y z hy hz _
  exact h F x y z hy hz

/-- Induced subsystems inherit global singleton-valuedness. -/
theorem System.induce_singleValued
    {A : System L.graph P V} {S : Set V}
    (h : A.FunctionOutputSingleValued) :
    (A.induce S).FunctionOutputSingleValued := by
  intro F x y z hy hz
  apply Subtype.ext
  exact h F (Subtype.val ∘ x) y.1 z.1 hy hz

/-- Restricting to a set of parts inherits global singleton-valuedness. -/
theorem System.restrict_singleValued
    {Q : Type v}
    {A : System L.graph P V}
    (α : Q ↪ P)
    (h : A.FunctionOutputSingleValued) :
    (A.restrict α).FunctionOutputSingleValued := by
  exact System.induce_singleValued h

/-- Relabelling parts changes no relation tuples. -/
theorem System.relabel_singleValued
    {Q : Type v}
    {A : System L.graph P V}
    (α : P ↪ Q)
    (h : A.FunctionOutputSingleValued) :
    (A.relabel α).FunctionOutputSingleValued :=
  h

namespace Closed.Induced

/-- Positive coordinate powers preserve global singleton-valuedness. -/
theorem power_singleValued
    {A : RelStructure L.graph P}
    {B : System L.graph P V}
    {N : ℕ}
    (hN : 0 < N)
    (hB : B.FunctionOutputSingleValued) :
    (Partite.Induced.power B N).FunctionOutputSingleValued := by
  intro F x y z hy hz
  have hcoord : ∀ k, y.coord k = z.coord k := by
    intro k
    let args : Fin (L.funcArity F) → V :=
      fun i => (x i).coord k
    have hyk : B.rel (.inr F)
        (Structure.funcTuple args (y.coord k)) := by
      have h := hy k
      have ht :
          Structure.funcTuple args (y.coord k) =
            (fun j => (Structure.funcTuple x y j).coord k) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [args, Structure.funcTuple]
        · simp [args, Structure.funcTuple]
      rw [ht]
      exact h
    have hzk : B.rel (.inr F)
        (Structure.funcTuple args (z.coord k)) := by
      have h := hz k
      have ht :
          Structure.funcTuple args (z.coord k) =
            (fun j => (Structure.funcTuple x z j).coord k) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [args, Structure.funcTuple]
        · simp [args, Structure.funcTuple]
      rw [ht]
      exact h
    exact hB F args (y.coord k) (z.coord k) hyk hzk
  let k0 : Fin N := ⟨0, hN⟩
  have hp : y.part = z.part := by
    calc
      y.part = B.part (y.coord k0) := (y.belongs k0).symm
      _ = B.part (z.coord k0) := congrArg B.part (hcoord k0)
      _ = z.part := z.belongs k0
  exact Partite.NonInduced.Vertex.ext B hp hcoord

end Closed.Induced

namespace HalfClosed.Initial

/-- The ordinary-indexed initial disjoint union preserves global
singleton-valuedness for positive-arity functions. -/
theorem singleValued
    (B : RelStructure L.graph V)
    (D : RelStructure L.graph P)
    (hpos : L.PositiveFuncArity)
    (hB : B.FunctionOutputSingleValued) :
    (picture B D).FunctionOutputSingleValued := by
  intro F x y z hy hz
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  rcases hy with ⟨i, a, ha, heqa⟩
  rcases hz with ⟨j, b, hb, heqb⟩
  have hya := congrFun heqa (Fin.castSucc k0)
  have hzb := congrFun heqb (Fin.castSucc k0)
  have hidxa : (x k0).1 = i := by
    calc
      (x k0).1 =
          (Structure.funcTuple x y (Fin.castSucc k0)).1 := by
        rw [Structure.funcTuple_castSucc]
      _ = (((fun v => (i, v)) ∘ a) (Fin.castSucc k0)).1 :=
        congrArg Prod.fst hya
      _ = i := by rfl
  have hidxb : (x k0).1 = j := by
    calc
      (x k0).1 =
          (Structure.funcTuple x z (Fin.castSucc k0)).1 := by
        rw [Structure.funcTuple_castSucc]
      _ = (((fun v => (j, v)) ∘ b) (Fin.castSucc k0)).1 :=
        congrArg Prod.fst hzb
      _ = j := by rfl
  have hij : j = i := hidxb.symm.trans hidxa
  subst j
  let argsA : Fin (L.funcArity F) → V :=
    fun k => a (Fin.castSucc k)
  let argsB : Fin (L.funcArity F) → V :=
    fun k => b (Fin.castSucc k)
  let outA : V := a (Fin.last (L.funcArity F))
  let outB : V := b (Fin.last (L.funcArity F))
  have hargs : argsA = argsB := by
    funext k
    have hka := congrArg Prod.snd (congrFun heqa (Fin.castSucc k))
    have hkb := congrArg Prod.snd (congrFun heqb (Fin.castSucc k))
    have ha0 : (x k).2 = argsA k := by
      simpa [argsA, Function.comp_apply] using hka
    have hb0 : (x k).2 = argsB k := by
      simpa [argsB, Function.comp_apply] using hkb
    exact ha0.symm.trans hb0
  have hrelA : B.rel (.inr F)
      (Structure.funcTuple argsA outA) := by
    have heta : Structure.funcTuple argsA outA = a := by
      simpa [argsA, outA, Language.graph] using
        (Structure.funcTuple_eta (t := a))
    rw [heta]
    exact ha
  have hrelB0 : B.rel (.inr F)
      (Structure.funcTuple argsB outB) := by
    have heta : Structure.funcTuple argsB outB = b := by
      simpa [argsB, outB, Language.graph] using
        (Structure.funcTuple_eta (t := b))
    rw [heta]
    exact hb
  have hrelB : B.rel (.inr F)
      (Structure.funcTuple argsA outB) := by
    rw [hargs]
    exact hrelB0
  have hout : outA = outB := hB F argsA outA outB hrelA hrelB
  have hyEq : y = (i, outA) := by
    have h := congrFun heqa (Fin.last (L.funcArity F))
    rw [Structure.funcTuple_last] at h
    change y = (i, outA) at h
    exact h
  have hzEq : z = (i, outB) := by
    have h := congrFun heqb (Fin.last (L.funcArity F))
    rw [Structure.funcTuple_last] at h
    change z = (i, outB) at h
    exact h
  calc
    y = (i, outA) := hyEq
    _ = (i, outB) := congrArg (fun q => (i, q)) hout
    _ = z := hzEq.symm

end HalfClosed.Initial

namespace Closed.Attachment

/-- Closed free attachment preserves global singleton-valuedness. -/
theorem singleValued
    {I : Type v}
    {B : Partite.System L.graph P V}
    {S : Set V}
    {D : Partite.System L.graph P W}
    {f : I → Partite.Closed.Embedding (B.induce S) D}
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hB : B.FunctionOutputSingleValued)
    (hD : D.FunctionOutputSingleValued) :
    (attach B S D f).FunctionOutputSingleValued := by
  classical
  intro F x y z hy hz
  let g := relMaps (f := f)
  by_cases hcore : ∀ k, ∃ a : W, x k = Sum.inl a
  · choose a ha using hcore
    have hargs : x = Sum.inl ∘ a := by
      funext k
      exact ha k
    have hy' :
        (RelStructure.Attachment.attach
          B.toRelStructure S D.toRelStructure g).rel
          (.inr F)
          (Structure.funcTuple (Sum.inl ∘ a) y) := by
      rw [← hargs]
      exact hy
    have hz' :
        (RelStructure.Attachment.attach
          B.toRelStructure S D.toRelStructure g).rel
          (.inr F)
          (Structure.funcTuple (Sum.inl ∘ a) z) := by
      rw [← hargs]
      exact hz
    obtain ⟨yy, hyy, hyout⟩ :=
      core_closed (B := B) (S := S) (D := D) (f := f) hS
        F a y hy'
    obtain ⟨zz, hzz, hzout⟩ :=
      core_closed (B := B) (S := S) (D := D) (f := f) hS
        F a z hz'
    have heq := hD F a yy zz hyy hzz
    calc
      y = Sum.inl yy := hyout.symm
      _ = Sum.inl zz := congrArg Sum.inl heq
      _ = z := hzout
  · push Not at hcore
    obtain ⟨k, hk⟩ := hcore
    cases hx : x k with
    | inl a => exact (hk a hx).elim
    | inr p =>
        let i := p.1
        let outside := p.2
        have getCopy :
            ∀ {t : Vertex S W I},
              (RelStructure.Attachment.attach
                B.toRelStructure S D.toRelStructure g).rel
                (.inr F) (Structure.funcTuple x t) →
              ∃ args : Fin (L.funcArity F) → V, ∃ out : V,
                B.rel (.inr F) (Structure.funcTuple args out) ∧
                x = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i ∘ args ∧
                t = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i out := by
          intro t ht
          have hk' :
              (Structure.funcTuple x t) (Fin.castSucc k) =
                Sum.inr (i, outside) := by
            simpa [i, outside, Structure.funcTuple] using hx
          obtain ⟨q, hq, heq⟩ :=
            RelStructure.Attachment.relation_eq_copy_of_contains_outside
              (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
              (f := g) ht (Fin.castSucc k) i outside hk'
          let args : Fin (L.funcArity F) → V :=
            fun j => q (Fin.castSucc j)
          let out : V := q (Fin.last (L.funcArity F))
          have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
            have heta : Structure.funcTuple args out = q := by
              simpa [args, out, Language.graph] using
                (Structure.funcTuple_eta (t := q))
            rw [heta]
            exact hq
          have hargs :
              x = RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i ∘ args := by
            funext j
            have hj := congrFun heq (Fin.castSucc j)
            rw [Structure.funcTuple_castSucc] at hj
            exact hj
          have hout :
              t = RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i out := by
            have hj := congrFun heq (Fin.last (L.funcArity F))
            rw [Structure.funcTuple_last] at hj
            exact hj
          exact ⟨args, out, hrel, hargs, hout⟩
        obtain ⟨ay, byv, hry, hargsY, houtY⟩ := getCopy hy
        obtain ⟨az, bz, hrz, hargsZ, houtZ⟩ := getCopy hz
        have hargsEq : ay = az := by
          funext j
          apply RelStructure.Attachment.copyMap_injective
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i
          have hj := congrFun (hargsY.symm.trans hargsZ) j
          simpa [Function.comp_apply] using hj
        subst az
        have houtEq := hB F ay byv bz hry hrz
        calc
          y = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i byv := houtY
          _ = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i bz :=
              congrArg
                (RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i) houtEq
          _ = z := houtZ.symm

end Closed.Attachment

namespace Nested

/-- Flattening changes only the part map, so global singleton-valuedness is
unchanged. -/
theorem flatten_singleValued
    (O : Partite.System L.graph P W)
    (C : Partite.System L.graph W X)
    (hC : C.IsPartiteOver O.toRelStructure)
    (h : C.FunctionOutputSingleValued) :
    (flatten O C hC).FunctionOutputSingleValued :=
  h

end Nested

/-- Adding unary part predicates does not change function graph relations. -/
theorem singleValued_expandFunctional
    {A : Partite.System L.graph P V}
    (h : A.FunctionOutputSingleValued) :
    A.expandFunctional.toRelStructure.FunctionOutputSingleValued := by
  intro F x y z hy hz
  exact h F.down x y z hy hz

/-- Forgetting unary part predicates does not change function graph
relations. -/
theorem singleValued_ofFunctionalExpansion
    {Q : Type v}
    {C : Partite.System (L.withParts P).graph Q V}
    (h : C.toRelStructure.FunctionOutputSingleValued) :
    (C.ofFunctionalExpansion).FunctionOutputSingleValued := by
  intro F x y z hy hz
  exact h (ULift.up F) x y z hy hz

end Partite
end StructuralRamsey
