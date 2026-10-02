import PartiteConstruction.Functional.ClosedPicture
import PartiteConstruction.Partite.Picture

/-! # Disjoint-copy repair for arbitrary projected pictures

An ordinary Picture witness can be repaired without freely attaching along a
non-U-closed support.  The repair uses a disjoint union of copies of the current
partite system, indexed by its embeddings into the ordinary Picture witness.
For positive-arity functions every indexed copy is U-closed, and
U-transversality is inherited from the copied system.

A finite vector-colouring of A-copies in the ordinary witness then chooses an
index whose corresponding disjoint copy is monochromatic for the original
closed colouring.  This avoids the non-closed free-attachment obstruction.
-/
namespace StructuralRamsey.Partite.ClosedRepair

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V I : Type v}

/-- Disjoint union of copies of a partite system, preserving its original
partition labels. -/
def disjointCopies (B : Partite.System L.graph P V) (I : Type v) :
    Partite.System L.graph P (I × V) where
  rel R z := ∃ i x, B.rel R x ∧ z = (fun v => (i, v)) ∘ x
  part iv := B.part iv.2
  transversal R z hz k l hkl := by
    obtain ⟨i, x, hx, rfl⟩ := hz
    have hxy := B.transversal R x hx k l hkl
    exact congrArg (fun v => (i, v)) hxy

/-- The canonical indexed copy as a partite embedding. -/
def copyEmbedding
    (B : Partite.System L.graph P V) (I : Type v) (i : I) :
    Partite.Embedding B (disjointCopies B I) where
  toFun v := (i, v)
  injective _ _ h := congrArg Prod.snd h
  map_rel_iff R x := by
    constructor
    · rintro ⟨j, y, hy, h⟩
      have heq : x = y := funext (fun k => congrArg Prod.snd (congrFun h k))
      simpa only [heq] using hy
    · intro hx
      exact ⟨i, x, hx, rfl⟩
  map_part _ := rfl

/-- For positive-arity function symbols an indexed copy in the disjoint union
is U-closed: an input coordinate fixes the copy index. -/
def closedCopyEmbedding
    (B : Partite.System L.graph P V) (I : Type v)
    (hpos : L.PositiveFuncArity) (i : I) :
    Partite.Closed.Embedding B (disjointCopies B I) := by
  let pe := copyEmbedding B I i
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  change
    (disjointCopies B I).rel (.inr F)
      (Structure.funcTuple (pe ∘ x) y) at hy
  rcases hy with ⟨j, t, ht, heq⟩
  have hidx : j = i := by
    have hk := congrFun heq (Fin.castSucc k0)
    have hk' := congrArg Prod.fst hk
    have hij : i = j := by
      calc
        i = (Structure.funcTuple (pe ∘ x) y (Fin.castSucc k0)).1 := by
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
      x k = (Structure.funcTuple (pe ∘ x) y (Fin.castSucc k)).2 := by
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
    pe z = (i, z) := rfl
    _ = (((fun v => (i, v)) ∘ t) (Fin.last (L.funcArity F))) := by rfl
    _ = Structure.funcTuple (pe ∘ x) y (Fin.last (L.funcArity F)) :=
      hout.symm
    _ = y := Structure.funcTuple_last _ _

/-- Disjoint copies inherit U-transversality from the copied system. -/
theorem disjointCopies_uTransversal
    (B : Partite.System L.graph P V) (I : Type v)
    (hpos : L.PositiveFuncArity)
    (hU : B.FunctionOutputTransversal) :
    (disjointCopies B I).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  rcases hy with ⟨i, a, ha, heqa⟩
  rcases hz with ⟨j, b, hb, heqb⟩
  have hya := congrFun heqa (Fin.castSucc k0)
  have hzb := congrFun heqb (Fin.castSucc k0)
  have hidxa : (x k0).1 = i := by
    calc
      (x k0).1 = (Structure.funcTuple x y (Fin.castSucc k0)).1 := by
        rw [Structure.funcTuple_castSucc]
      _ = (((fun v => (i, v)) ∘ a) (Fin.castSucc k0)).1 :=
        congrArg Prod.fst hya
      _ = i := by rfl
  have hidxb : (x k0).1 = j := by
    calc
      (x k0).1 = (Structure.funcTuple x z (Fin.castSucc k0)).1 := by
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
  have hpB : B.part ay = B.part bz := by
    have hp' := hp
    rw [hyEq, hzEq] at hp'
    exact hp'
  have heq : ay = bz := by
    let args : Fin (L.funcArity F) → V :=
      fun k => (x k).2
    have hargsA : args = fun k => a (Fin.castSucc k) := by
      funext k
      have hk := congrArg Prod.snd (congrFun heqa (Fin.castSucc k))
      simpa [args, Structure.funcTuple] using hk
    have hargsB : args = fun k => b (Fin.castSucc k) := by
      funext k
      have hk := congrArg Prod.snd (congrFun heqb (Fin.castSucc k))
      simpa [args, Structure.funcTuple] using hk
    have ha' : B.rel (.inr F) (Structure.funcTuple args ay) := by
      have heta : Structure.funcTuple (fun k => a (Fin.castSucc k)) ay = a := by
        simpa [ay, Language.graph] using (Structure.funcTuple_eta (t := a))
      rw [hargsA, heta]
      exact ha
    have hb' : B.rel (.inr F) (Structure.funcTuple args bz) := by
      have heta : Structure.funcTuple (fun k => b (Fin.castSucc k)) bz = b := by
        simpa [bz, Language.graph] using (Structure.funcTuple_eta (t := b))
      rw [hargsB, heta]
      exact hb
    exact hU F args ay bz ha' hb' hpB
  calc
    y = (i, ay) := hyEq
    _ = (i, bz) := congrArg (fun q => (i, q)) heq
    _ = z := hzEq.symm

end StructuralRamsey.Partite.ClosedRepair
