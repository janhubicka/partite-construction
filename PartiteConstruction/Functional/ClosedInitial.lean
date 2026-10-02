import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Initial
import PartiteConstruction.Partite.InducedInitial

/-! # U-closed initial pictures

For positive-arity functions, a relation tuple encoding a function value has at
least one input coordinate. In a disjoint union of copies this input fixes the
copy index, so each copy is U-closed and the whole initial picture is
U-transversal. Nullary functions are exactly the exceptional case.
-/
namespace StructuralRamsey.Partite.Closed.Initial

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable (B : RelStructure L.graph V) (D : RelStructure L.graph P)

abbrev Index := RelStructure.ClosedEmbedding B D

def β (e : Index B D) : V ↪ P :=
  e.toEmbedding.toFunctionEmbedding

def picture : Partite.System L.graph P (Index B D × V) :=
  Partite.Initial.picture B (β B D)

/-- Every indexed initial copy is U-closed when function arities are positive. -/
def copyEmbedding
    (hpos : L.PositiveFuncArity)
    (i : Index B D) :
    RelStructure.ClosedEmbedding B (picture B D).toRelStructure where
  toEmbedding := Partite.Initial.copyEmbedding B (β B D) i
  closed := by
    intro F x y hy
    have hF : 0 < L.funcArity F := hpos F
    let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
    change
      (picture B D).rel (.inr F)
        (Structure.funcTuple
          ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y) at hy
    rcases hy with ⟨j, t, ht, heq⟩
    have hidx : j = i := by
      have hk := congrFun heq (Fin.castSucc k0)
      have hk' := congrArg Prod.fst hk
      have hij : i = j := by
        simpa [Structure.funcTuple, Function.comp_apply,
          Partite.Initial.copyEmbedding] using hk'
      exact hij.symm
    subst j
    let args : Fin (L.funcArity F) → V :=
      fun k => t (Fin.castSucc k)
    let z : V := t (Fin.last (L.funcArity F))
    have hargs : x = args := by
      funext k
      have hk := congrFun heq (Fin.castSucc k)
      have hk' := congrArg Prod.snd hk
      simpa [args, Structure.funcTuple, Function.comp_apply,
        Partite.Initial.copyEmbedding] using hk'
    have heta : Structure.funcTuple args z = t := by
      simpa [args, z, Language.graph] using
        (Structure.funcTuple_eta (t := t))
    have hrel : B.rel (.inr F) (Structure.funcTuple x z) := by
      rw [hargs, heta]
      exact ht
    refine ⟨z, hrel, ?_⟩
    have hout := congrFun heq (Fin.last (L.funcArity F))
    have hout' : y = (i, z) := by
      simpa [z, Structure.funcTuple, Function.comp_apply,
        Partite.Initial.copyEmbedding] using hout
    exact hout'.symm

/-- The disjoint-union initial picture is U-transversal for positive-arity
functions. -/
theorem uTransversal
    (hpos : L.PositiveFuncArity) :
    (picture B D).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  rcases hy with ⟨i, a, ha, heqa⟩
  rcases hz with ⟨j, b, hb, heqb⟩
  have hij : i = j := by
    have hya := congrFun heqa (Fin.castSucc k0)
    have hzb := congrFun heqb (Fin.castSucc k0)
    have hi :
        (i, a (Fin.castSucc k0)) = x k0 := by
      symm
      simpa [Structure.funcTuple, Function.comp_apply] using hya
    have hj :
        (j, b (Fin.castSucc k0)) = x k0 := by
      symm
      simpa [Structure.funcTuple, Function.comp_apply] using hzb
    exact congrArg Prod.fst (hi.trans hj.symm)
  subst j
  let ay : V := a (Fin.last (L.funcArity F))
  let bz : V := b (Fin.last (L.funcArity F))
  have houta : y = (i, ay) := by
    have h := congrFun heqa (Fin.last (L.funcArity F))
    simpa [ay, Structure.funcTuple, Function.comp_apply] using h
  have houtb : z = (i, bz) := by
    have h := congrFun heqb (Fin.last (L.funcArity F))
    simpa [bz, Structure.funcTuple, Function.comp_apply] using h
  have hp' := hp
  rw [houta, houtb] at hp'
  have hpart : (β B D i) ay = (β B D i) bz := hp'
  have houtEq : ay = bz := (β B D i).injective hpart
  calc
    y = (i, ay) := houta
    _ = (i, bz) := congrArg (fun q => (i, q)) houtEq
    _ = z := houtb.symm

/-- The initial picture is relationally D-partite. -/
theorem isPartiteOver [Nonempty (Index B D)] :
    (picture B D).IsPartiteOver D :=
  Partite.Induced.Initial.picture_isPartiteOver
    (B := B) D (fun e : Index B D => e.toEmbedding)

end StructuralRamsey.Partite.Closed.Initial
