import PartiteConstruction.Iterated.WeakStepProjectedPartial
import PartiteConstruction.Partite.InducedConstruction
import PartiteConstruction.Iterated.TreeCompletion

/-! # Tree-completion invariants for the actual induced-construction trace

The actual induced construction stores each Picture transition through
`BasedOn`.  The canonical tree-completion theorem transfers across the
recorded isomorphism, so local tree completability propagates through the
heterogeneous trace returned by `inducedConstruction`.

Only the fixed base D needs projected-partial coherence at level n-1.  The
moving Picture stages carry only local tree completability at level n.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- A stage based on one canonical Picture step inherits local tree
completability. -/
theorem basedStep_locallyTreeCompletable_projectedPartial
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (C₁ : Partite.System L P Y)
    [Finite U] [Finite V] [Finite P] [Finite X]
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id (n - 1))
    (hC₀ : RelStructure.LocallyTreeCompletable B C₀.toRelStructure n)
    (hPartite : C₀.IsPartiteOver D)
    (hBased : Partite.Induced.BasedOn A D C₀ α C₁) :
    RelStructure.LocallyTreeCompletable B C₁.toRelStructure n := by
  rcases hBased with ⟨N, hN, ⟨iso⟩⟩
  have hCanonical :=
    canonicalStep_locallyTreeCompletable_projectedPartial
      A B D C₀ α hA eAB n hn hD hC₀ hPartite N hN
  exact hCanonical.pullback_embedding iso.toRelEmbedding

end StructuralRamsey.Partite.Iterated

namespace StructuralRamsey.Partite.Induced.Trace

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- Local tree completability propagates along the actual heterogeneous trace
when the fixed base carries projected-partial coherence one level lower. -/
theorem locallyTreeCompletable_projectedPartial
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L P}
    {S T : Partite.Induced.Stage B D}
    {xs : List (Partite.Induced.RelevantEmbedding A B D)}
    (hTrace : Partite.Induced.Trace A B D S xs T)
    [Finite U] [Finite V] [Finite P]
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id (n - 1))
    (hS : RelStructure.LocallyTreeCompletable B S.system.toRelStructure n) :
    RelStructure.LocallyTreeCompletable B T.system.toRelStructure n := by
  induction hTrace with
  | nil =>
      exact hS
  | @snoc T R xs h α hBased ih =>
      exact Partite.Iterated.basedStep_locallyTreeCompletable_projectedPartial
        A B D T.system α.1 R.system
        hA eAB n hn hD ih T.isPartite hBased

end StructuralRamsey.Partite.Induced.Trace

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- The concrete induced-partite construction preserves the Ramsey arrow and
produces property-(2) local tree completability from projected-history
coherence of the fixed base. -/
theorem inducedConstruction_locallyTreeCompletable_projectedPartial
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ)
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id (n - 1)) :
    letI : Nonempty (RelStructure.Embedding B D) :=
      nonempty_embedding_of_arrow A B D κ hRamsey
    let S₀ := initialStage B D
    ∃ T : Stage B D,
      Trace A B D S₀ (allRelevant A B D).reverse T ∧
      StructuralRamsey.Arrow A B T.system.toRelStructure κ ∧
      RelStructure.LocallyTreeCompletable B T.system.toRelStructure n := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D
  obtain ⟨T, hTrace, hArrow⟩ :=
    inducedConstruction A B D κ hRamsey
  have hInitial :
      RelStructure.LocallyTreeCompletable B S₀.system.toRelStructure n := by
    exact RelStructure.LocallyTreeCompletable.initial
      B (fun β : RelStructure.Embedding B D => β.toFunctionEmbedding) n
  have hLocal :
      RelStructure.LocallyTreeCompletable B T.system.toRelStructure n :=
    hTrace.locallyTreeCompletable_projectedPartial hA eAB n hn hD hInitial
  exact ⟨T, hTrace, hArrow, hLocal⟩

end StructuralRamsey.Partite.Induced
