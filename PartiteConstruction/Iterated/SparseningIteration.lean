import PartiteConstruction.Iterated.InducedTraceLocal
import PartiteConstruction.Iterated.ProjectedCover

/-! # Iterating the actual induced construction

This file packages repeated applications of the actual
\`Partite.Induced.inducedConstruction\`.  After the first application the
state records four facts simultaneously:

* the Ramsey arrow survives;
* the composite projection is a homomorphism-embedding into the original
  witness \`Q\`;
* local tree-likeness has reached the current level;
* every irreducible projects into a copy of \`B\` in \`Q\`.

The last invariant is propagated through later stages by
\`ProjectsIrreduciblesInto.precomp\`.
-/
namespace StructuralRamsey.Partite.IteratedSparsening

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (Q : RelStructure L P)
variable (κ : Type*)

/-- A positive-level state of the iterated induced construction. -/
structure Stage (level : ℕ) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  C : RelStructure L Vertex
  arrow : StructuralRamsey.Arrow A B C κ
  projection : Vertex → P
  projectionHE : C.IsHomomorphismEmbedding Q projection
  locallyTreeLike : RelStructure.LocallyTreeLike A B C level
  projected :
    RelStructure.ProjectsIrreduciblesInto B C Q projection

attribute [instance] Stage.finiteVertex

/-- The first induced construction raises local tree-likeness from level zero
to level one and establishes projected irreducible coverage in \`Q\`. -/
theorem first
    [Finite UA] [Finite VB] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B Q κ)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B) :
    ∃ S : Stage A B Q κ 1, True := by
  classical
  letI : Nonempty (RelStructure.Embedding B Q) :=
    Partite.Induced.nonempty_embedding_of_arrow A B Q κ hRamsey
  let β : RelStructure.Embedding B Q :=
    Classical.choice (inferInstance : Nonempty (RelStructure.Embedding B Q))
  have hZero : RelStructure.LocallyTreeLike A B Q 0 :=
    RelStructure.LocallyTreeLike.zero_of_embeddings eAB β
  obtain ⟨T, hTrace, hArrow, hLocal⟩ :=
    Partite.Induced.inducedConstruction_locallyTreeLike
      A B Q κ hRamsey hA eAB 1 (by omega) hZero
  let S : Stage A B Q κ 1 := {
    Vertex := T.Vertex
    finiteVertex := T.finiteVertex
    C := T.system.toRelStructure
    arrow := hArrow
    projection := T.system.part
    projectionHE := T.isPartite
    locallyTreeLike := hLocal
    projected :=
      Partite.Induced.projectsIrreduciblesInto_of_covers
        B Q T.system T.covers
  }
  exact ⟨S, trivial⟩

/-- One further induced construction raises the local-tree level by one while
composing the projection and preserving projected irreducible coverage. -/
theorem succ
    [Finite UA] [Finite VB] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (k : ℕ) (S : Stage A B Q κ k) :
    ∃ T : Stage A B Q κ (k + 1), True := by
  classical
  have hD :
      RelStructure.LocallyTreeLike A B S.C ((k + 1) - 1) := by
    simpa using S.locallyTreeLike
  obtain ⟨R, hTrace, hArrow, hLocal⟩ :=
    Partite.Induced.inducedConstruction_locallyTreeLike
      A B S.C κ S.arrow hA eAB (k + 1) (by omega) hD
  let q : R.Vertex → S.Vertex := R.system.part
  let p : R.Vertex → P := S.projection ∘ q
  have hp : R.system.toRelStructure.IsHomomorphismEmbedding Q p := by
    exact S.projectionHE.comp R.isPartite
  have hProjected :
      RelStructure.ProjectsIrreduciblesInto
        B R.system.toRelStructure Q p := by
    exact S.projected.precomp R.isPartite
  let T : Stage A B Q κ (k + 1) := {
    Vertex := R.Vertex
    finiteVertex := R.finiteVertex
    C := R.system.toRelStructure
    arrow := hArrow
    projection := p
    projectionHE := hp
    locallyTreeLike := hLocal
    projected := hProjected
  }
  exact ⟨T, trivial⟩

/-- Iterate the induced construction to any positive local-tree level. -/
theorem build
    [Finite UA] [Finite VB] [Finite P]
    [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B Q κ)
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
        simpa using first A B Q κ hRamsey hA eAB
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        obtain ⟨S, _⟩ := ih hkpos
        simpa [Nat.succ_eq_add_one] using
          succ A B Q κ hA eAB k S

end StructuralRamsey.Partite.IteratedSparsening
