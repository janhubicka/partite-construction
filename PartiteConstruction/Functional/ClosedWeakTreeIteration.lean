import PartiteConstruction.Functional.ClosedConstructionWeakTreeStrong
import PartiteConstruction.Iterated.Initial
import PartiteConstruction.Iterated.WeakLocalTreeLike
import PartiteConstruction.Iterated.WeakFunctionalTreeCompletion

/-! # Iterating the actual U-closed functional partite construction

Under hereditary irreducibility of the *graph* control A, the full controlled
LocallyTreeLike invariant propagates through one complete U-closed induced
partite construction with a one-vertex rank gain.

Each stage records simultaneously:
* the **full functional** Ramsey arrow, via U-closed graph embeddings;
* the current bound on all **weak** vertex-test graph tree completions,
  including the intersection control needed for the next iteration;
* a relational graph homomorphism-embedding to the original witness.

The function-graph completion must not be mistaken for a fibre-surjective
homomorphism into a genuine strict functional tree.
-/

namespace StructuralRamsey.Partite.Closed.IteratedWeak

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {U V P : Type v}
variable (A : RelStructure L.graph U)
variable (B : RelStructure L.graph V)
variable (Q : RelStructure L.graph P)
variable (κ : Type*)

/-- A stage of repeated actual U-closed functional induced constructions,
with its original-control projection and weak test-size bound. -/
structure Stage (level : ℕ) where
  Carrier : Type v
  finiteCarrier : Finite Carrier
  C : RelStructure L.graph Carrier
  arrow : RelStructure.ClosedArrow A B C κ
  projection : Carrier → P
  projectionHE : C.IsHomomorphismEmbedding Q projection
  locallyTreeLike : RelStructure.LocallyTreeLike A B C level

attribute [instance] Stage.finiteCarrier

/-- First full U-closed pass establishes the weak graph local-tree bound 1. -/
theorem first
    [Finite U] [Finite V] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.ClosedArrow A B Q κ)
    (hpos : L.PositiveFuncArity)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B) :
    ∃ S : Stage A B Q κ 1, True := by
  classical
  letI : Nonempty (RelStructure.ClosedEmbedding B Q) :=
    Partite.Closed.Construction.nonempty_embedding_of_arrow A B Q κ hRamsey
  let β : RelStructure.ClosedEmbedding B Q :=
    Classical.choice (inferInstance : Nonempty (RelStructure.ClosedEmbedding B Q))
  have hZero : RelStructure.LocallyTreeLike A B Q 0 :=
    RelStructure.LocallyTreeLike.zero_of_embeddings eAB β.toEmbedding
  obtain ⟨T, hArrow, hLocal⟩ :=
    Partite.Closed.Construction.inducedConstruction_withStrongTree
      A B Q hpos κ hRamsey hA eAB 1 (by omega) (by simpa using hZero)
  let S : Stage A B Q κ 1 := {
    Carrier := T.Vertex
    finiteCarrier := T.finiteVertex
    C := T.system.toRelStructure
    arrow := hArrow
    projection := T.system.part
    projectionHE := T.isPartite
    locallyTreeLike := hLocal
  }
  exact ⟨S, trivial⟩

/-- Each further complete U-closed induced pass raises the weak rank one,
while preserving the full closed Ramsey arrow and projection to Q. -/
theorem succ
    [Finite U] [Finite V] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hpos : L.PositiveFuncArity)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (k : ℕ) (S : Stage A B Q κ k) :
    ∃ T : Stage A B Q κ (k + 1), True := by
  classical
  letI : Finite S.Carrier := S.finiteCarrier
  have hD : RelStructure.LocallyTreeLike A B S.C ((k + 1) - 1) := by
    simpa using S.locallyTreeLike
  obtain ⟨R, hArrow, hLocal⟩ :=
    Partite.Closed.Construction.inducedConstruction_withStrongTree
      A B S.C hpos κ S.arrow hA eAB (k + 1) (by omega) hD
  let q : R.Vertex → S.Carrier := R.system.part
  let p : R.Vertex → P := S.projection ∘ q
  have hp : R.system.toRelStructure.IsHomomorphismEmbedding Q p := by
    exact S.projectionHE.comp R.isPartite
  let T : Stage A B Q κ (k + 1) := {
    Carrier := R.Vertex
    finiteCarrier := R.finiteVertex
    C := R.system.toRelStructure
    arrow := hArrow
    projection := p
    projectionHE := hp
    locallyTreeLike := hLocal
  }
  exact ⟨T, trivial⟩

/-- After n complete U-closed functional passes, every weak graph test on at
most n vertices has the controlled relational tree completion. -/
theorem build
    [Finite U] [Finite V] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hRamsey : RelStructure.ClosedArrow A B Q κ)
    (hpos : L.PositiveFuncArity)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ S : Stage A B Q κ n, True := by
  classical
  induction n with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simpa using first A B Q κ hRamsey hpos hA eAB
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        obtain ⟨S, _⟩ := ih hkpos
        simpa [Nat.succ_eq_add_one] using
          succ A B Q κ hpos hA eAB k S

end StructuralRamsey.Partite.Closed.IteratedWeak

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Full functional Ramsey witnesses can be obtained after any positive
number of actual U-closed induced passes, with an n-vertex controlled
weak-substructure **graph** tree bound and a graph homomorphism-embedding
to the original D. -/
theorem inducedRamsey_iteratedWeakGraph
    (A : Structure L U)
    (B : Structure L V)
    (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      Structure.Arrow A B C κ ∧
      WeakLocallyTreeLike A B C n ∧
      ∃ p : W → P, C.graph.IsHomomorphismEmbedding D.graph p := by
  classical
  have hClosed : RelStructure.ClosedArrow A.graph B.graph D.graph κ :=
    (Structure.arrow_iff_closedGraph (A := A) (B := B) D κ).mp hRamsey
  obtain ⟨S, _⟩ :=
    Partite.Closed.IteratedWeak.build
      A.graph B.graph D.graph κ hClosed hpos hA eAB.graph n hn
  let C : Structure L S.Carrier := Structure.ofGraph S.C
  have hArrow : Structure.Arrow A B C κ :=
    (Structure.arrow_ofGraph_iff_closed
      (A := A) (B := B) S.C κ).mpr S.arrow
  have hWeak : WeakLocallyTreeLike A B C n :=
    S.locallyTreeLike.pullback_embedding
      (Structure.ofGraphGraphEmbedding S.C)
  have hp : C.graph.IsHomomorphismEmbedding D.graph S.projection :=
    S.projectionHE.comp
      (Structure.ofGraphGraphEmbedding S.C).isHomomorphismEmbedding
  exact ⟨S.Carrier, S.finiteCarrier, C, hArrow, hWeak, S.projection, hp⟩

end StructuralRamsey.Structure
