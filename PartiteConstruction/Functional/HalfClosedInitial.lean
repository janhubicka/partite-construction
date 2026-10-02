import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Initial
import PartiteConstruction.Partite.InducedInitial

/-! # Half-closed initial pictures

The recursive construction needs an initial disjoint union indexed by ordinary
embeddings `B -> D`, because the half-closed Ramsey hypothesis may return a
copy of `B` whose projection to `D` is not U-closed.

The copy of `B` inside the disjoint union is nevertheless U-closed whenever
all function symbols have positive arity: an input coordinate determines the
copy index.  The same argument gives U-transversality of the whole picture.
-/
namespace StructuralRamsey.Partite.HalfClosed.Initial

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable (B : RelStructure L.graph V) (D : RelStructure L.graph P)

/-- Ordinary (not necessarily U-closed) copies of B in D. -/
abbrev Index := RelStructure.Embedding B D

def β (e : Index B D) : V ↪ P :=
  e.toFunctionEmbedding

def picture : Partite.System L.graph P (Index B D × V) :=
  Partite.Initial.picture B (β B D)

/-- Every indexed copy is U-closed inside the disjoint union, even though its
projection to D need not be U-closed. -/
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
        calc
          i = (Structure.funcTuple
                ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y
                (Fin.castSucc k0)).1 := by
            rw [Structure.funcTuple_castSucc]
            rfl
          _ = (((fun v => (j, v)) ∘ t) (Fin.castSucc k0)).1 := hk'
          _ = j := by rfl
      exact hij.symm
    subst j
    let args : Fin (L.funcArity F) → V :=
      fun k => t (Fin.castSucc k)
    let z : V := t (Fin.last (L.funcArity F))
    have hargs : x = args := by
      funext k
      have hk := congrFun heq (Fin.castSucc k)
      have hk' := congrArg Prod.snd hk
      calc
        x k =
            (Structure.funcTuple
              ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y
              (Fin.castSucc k)).2 := by
          rw [Structure.funcTuple_castSucc]
          rfl
        _ = (((fun v => (i, v)) ∘ t) (Fin.castSucc k)).2 := hk'
        _ = t (Fin.castSucc k) := by rfl
        _ = args k := by rfl
    have heta : Structure.funcTuple args z = t := by
      simpa [args, z, Language.graph] using
        (Structure.funcTuple_eta (t := t))
    have hrel : B.rel (.inr F) (Structure.funcTuple x z) := by
      rw [hargs, heta]
      exact ht
    refine ⟨z, hrel, ?_⟩
    have hout := congrFun heq (Fin.last (L.funcArity F))
    calc
      (Partite.Initial.copyEmbedding B (β B D) i) z =
          (i, z) := rfl
      _ = (((fun v => (i, v)) ∘ t)
            (Fin.last (L.funcArity F))) := by rfl
      _ = Structure.funcTuple
            ((Partite.Initial.copyEmbedding B (β B D) i) ∘ x) y
            (Fin.last (L.funcArity F)) := hout.symm
      _ = y := by
        rw [Structure.funcTuple_last]

/-- The disjoint-union picture is U-transversal for positive-arity
functions, independently of whether its projections are closed. -/
theorem uTransversal
    (hpos : L.PositiveFuncArity) :
    (picture B D).FunctionOutputTransversal := by
  intro F x y z hy hz hp
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
  rw [hij] at heqb hzb
  let ay : V := a (Fin.last (L.funcArity F))
  let bz : V := b (Fin.last (L.funcArity F))
  have houta := congrFun heqa (Fin.last (L.funcArity F))
  have houtb := congrFun heqb (Fin.last (L.funcArity F))
  have hyEq : y = (i, ay) := by
    calc
      y = Structure.funcTuple x y (Fin.last (L.funcArity F)) := by
        rw [Structure.funcTuple_last]
      _ = (((fun v => (i, v)) ∘ a)
            (Fin.last (L.funcArity F))) := houta
      _ = (i, ay) := by rfl
  have hzEq : z = (i, bz) := by
    calc
      z = Structure.funcTuple x z (Fin.last (L.funcArity F)) := by
        rw [Structure.funcTuple_last]
      _ = (((fun v => (i, v)) ∘ b)
            (Fin.last (L.funcArity F))) := houtb
      _ = (i, bz) := by rfl
  have hp' := hp
  rw [hyEq, hzEq] at hp'
  have hpart : (β B D i) ay = (β B D i) bz := hp'
  have houtEq : ay = bz := (β B D i).injective hpart
  calc
    y = (i, ay) := hyEq
    _ = (i, bz) := congrArg (fun q => (i, q)) houtEq
    _ = z := hzEq.symm

/-- The ordinary-indexed initial picture remains relationally D-partite. -/
theorem isPartiteOver [Nonempty (Index B D)] :
    (picture B D).IsPartiteOver D :=
  Partite.Induced.Initial.picture_isPartiteOver
    (B := B) D (fun e : Index B D => e)

/-- The indexed copy has exactly the requested ordinary projection. -/
@[simp] theorem part_copyEmbedding
    (hpos : L.PositiveFuncArity)
    (i : Index B D) (b : V) :
    (picture B D).part (copyEmbedding B D hpos i b) = i b := by
  rfl

end StructuralRamsey.Partite.HalfClosed.Initial
