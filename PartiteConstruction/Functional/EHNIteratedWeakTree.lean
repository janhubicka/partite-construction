import PartiteConstruction.Functional.EHNConstructionWeakTree

/-! # Iterating genuine functional EHN passes by weak vertex count

All intermediate structures interpret genuine set-valued functions and
each complete partite pass uses the native full-function Hales--Jewett
lemma, closed support restriction, and full free attachments.
No U-closed intermediate relational construction occurs.

The *local test* is nevertheless an arbitrary weak induced substructure
on at most n vertices; this is exactly graph induction, without taking
its function closure. A native EHN pass raises n by one while preserving
the original full function-language Ramsey arrow and the weak
homomorphism-embedding projection.
-/

namespace StructuralRamsey.FunctionalPartite.EHN.NativeIteratedWeak

open StructuralRamsey.Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- One iterated native EHN stage, with the full function-language Ramsey
arrow and a controlled graph-tree witness at vertex rank n. -/
structure Witness
    (K : Structure.StructureClass (L := L))
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    (κ : Type*) (n : ℕ) where
  Carrier : Type v
  finiteCarrier : Finite Carrier
  C : Structure L Carrier
  mem : K C
  arrow : Structure.Arrow A B C κ
  projection : Carrier → P
  projected : C.IsEHNHomomorphismEmbedding D projection
  weakTree : RelStructure.LocallyTreeLike A.graph B.graph C.graph n

attribute [instance] Witness.finiteCarrier

/-- The first entire genuine EHN pass gives one controlled weak vertex,
starting from the trivial rank-zero property of a full B-embedding. -/
theorem first
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B) :
    Nonempty (Witness K A B D κ 1) := by
  classical
  obtain ⟨β₀, _⟩ :=
    hRamsey (fun _ => Classical.choice (inferInstance : Nonempty κ))
  have hZero :
      RelStructure.LocallyTreeLike A.graph B.graph D.graph (1 - 1) := by
    simpa using
      (RelStructure.LocallyTreeLike.zero_of_embeddings eAB.graph β₀.graph)
  obtain ⟨T, hLocal, hArrow⟩ :=
    inducedConstruction_weakGraphLocallyTreeLike
      hK A B D hKA hKB hpos κ hRamsey hA eAB 1 (by omega) hZero
  let W : Witness K A B D κ 1 := {
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    mem := T.mem
    arrow := hArrow
    projection := T.system.part
    projected := T.isPartite
    weakTree := hLocal
  }
  exact ⟨W⟩

/-- A subsequent full native functional EHN pass raises the weak graph
local-tree vertex bound from n to n+1 and composes the weak projection
back to the original control structure D. -/
theorem succ
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (W : Witness K A B D κ n) :
    Nonempty (Witness K A B D κ (n + 1)) := by
  classical
  letI : Finite W.Carrier := W.finiteCarrier
  have hD' :
      RelStructure.LocallyTreeLike A.graph B.graph W.C.graph
        ((n + 1) - 1) := by
    simpa using W.weakTree
  obtain ⟨T, hLocal, hArrow⟩ :=
    inducedConstruction_weakGraphLocallyTreeLike
      hK A B W.C hKA hKB hpos κ W.arrow
      hA eAB (n + 1) (by omega) hD'
  let W' : Witness K A B D κ (n + 1) := {
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    mem := T.mem
    arrow := hArrow
    projection := W.projection ∘ T.system.part
    projected := W.projected.comp T.isPartite
    weakTree := hLocal
  }
  exact ⟨W'⟩

/-- After n positive full function-language EHN partite passes, all weak
vertex tests on at most n vertices have controlled graph-tree witnesses. -/
theorem build
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (Witness K A B D κ n) := by
  classical
  induction n with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simpa using first K hK A B D hKA hKB hpos κ hRamsey hA eAB
      · obtain ⟨W⟩ := ih (Nat.pos_of_ne_zero hk)
        simpa [Nat.succ_eq_add_one] using
          succ K hK A B D hKA hKB hpos κ hA eAB k W

end

end StructuralRamsey.FunctionalPartite.EHN.NativeIteratedWeak

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Direct, class-preserving, iterated partite construction with genuinely
set-valued functions. The final full Ramsey witness has the controlled
graph-tree completion property on arbitrary **weak** induced substructures
of size at most n and a weak EHN projection to the original D.

For real function-closed substructures the same vertex bound applies at the
graph level. A strict function-language tree target is a separate
output-closure obligation; it is not claimed by this theorem. -/
theorem inducedRamsey_directFunctionalWeakGraph
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A B C κ ∧
      RelStructure.LocallyTreeLike A.graph B.graph C.graph n ∧
      ∃ p : W → P, C.IsEHNHomomorphismEmbedding D p := by
  obtain ⟨W⟩ :=
    FunctionalPartite.EHN.NativeIteratedWeak.build
      K hK A B D hKA hKB hpos κ hRamsey hA eAB n hn
  exact ⟨W.Carrier, W.finiteCarrier, W.C, W.mem, W.arrow,
    W.weakTree, W.projection, W.projected⟩

end StructuralRamsey.Structure
