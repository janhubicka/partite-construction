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
    rcases hpos F with hF
    let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
    change
      (picture B D).rel (.inr F)
        (Structure.funcTuple
          ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y) at hy
    rcases hy with ⟨j, t, ht, heq⟩
    have hidx : j = i := by
      have hk := congrFun heq (Fin.castSucc k0)
      have hleft :
          Structure.funcTuple
            ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y
            (Fin.castSucc k0) =
          (i, x k0) := by
        simp [Structure.funcTuple, Function.comp_apply,
          Partite.Initial.copyEmbedding]
      have hright :
          ((fun v => (j, v)) ∘ t) (Fin.castSucc k0) =
          (j, t (Fin.castSucc k0)) := rfl
      rw [hleft, hright] at hk
      exact congrArg Prod.fst hk
    subst j
    let z : V := t (Fin.last (L.funcArity F))
    have hargs : ∀ k : Fin (L.funcArity F),
        x k = t (Fin.castSucc k) := by
      intro k
      have hk := congrFun heq (Fin.castSucc k)
      exact congrArg Prod.snd hk
    have hrel : B.rel (.inr F) (Structure.funcTuple x z) := by
      convert ht using 1
      funext q
      refine Fin.lastCases ?_ (fun k => ?_) q
      · rfl
      · exact (hargs k).symm
    refine ⟨z, hrel, ?_⟩
    have hout := congrFun heq (Fin.last (L.funcArity F))
    exact hout.symm

/-- The disjoint-union initial picture is U-transversal for positive-arity
functions. -/
theorem uTransversal
    (hpos : L.PositiveFuncArity) :
    (picture B D).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  rcases hpos F with hF
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  rcases hy with ⟨i, a, ha, heqa⟩
  rcases hz with ⟨j, b, hb, heqb⟩
  have hij : i = j := by
    have hya := congrFun heqa (Fin.castSucc k0)
    have hzb := congrFun heqb (Fin.castSucc k0)
    have hsame :
        (i, a (Fin.castSucc k0)) =
          (j, b (Fin.castSucc k0)) := by
      calc
        (i, a (Fin.castSucc k0)) =
            Structure.funcTuple x y (Fin.castSucc k0) := hya.symm
        _ = x k0 := by simp [Structure.funcTuple]
        _ = Structure.funcTuple x z (Fin.castSucc k0) := by
          simp [Structure.funcTuple]
        _ = (j, b (Fin.castSucc k0)) := hzb
    exact congrArg Prod.fst hsame
  subst j
  have houta := congrFun heqa (Fin.last (L.funcArity F))
  have houtb := congrFun heqb (Fin.last (L.funcArity F))
  have hpart :
      (β B D i) (a (Fin.last (L.funcArity F))) =
        (β B D i) (b (Fin.last (L.funcArity F))) := by
    change
      (picture B D).part (i, a (Fin.last (L.funcArity F))) =
        (picture B D).part (i, b (Fin.last (L.funcArity F)))
    rw [← houta, ← houtb]
    exact hp
  have houtEq :
      a (Fin.last (L.funcArity F)) =
        b (Fin.last (L.funcArity F)) :=
    (β B D i).injective hpart
  calc
    y = (i, a (Fin.last (L.funcArity F))) := houta
    _ = (i, b (Fin.last (L.funcArity F))) :=
      congrArg (fun q => (i, q)) houtEq
    _ = z := houtb.symm

/-- The initial picture is relationally D-partite. -/
theorem isPartiteOver :
    (picture B D).IsPartiteOver D :=
  Partite.Induced.Initial.picture_isPartiteOver D
    (fun e : Index B D => e.toEmbedding)

end StructuralRamsey.Partite.Closed.Initial
