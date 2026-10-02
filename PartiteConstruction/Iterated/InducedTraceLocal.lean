import PartiteConstruction.Iterated.WeakStep
import PartiteConstruction.Partite.InducedConstruction
import PartiteConstruction.Iterated.Initial

/-! # Local-tree invariants for the actual induced-construction trace

The induced construction stores each Picture step through the abstract
\`BasedOn\` predicate.  A based stage is isomorphic to a canonical positive
power/free-attachment step.  The canonical weak-substructure theorem therefore
transfers to every actual step and hence to the \`Induced.Trace\` returned by
\`inducedConstruction\`.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- Any stage based on a canonical Picture step inherits the checked
weak-substructure local-tree invariant. -/
theorem basedStep_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (C₁ : Partite.System L P Y)
    [Finite U] [Finite V] [Finite P] [Finite X]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hC₀ : RelStructure.LocallyTreeLike A B C₀.toRelStructure n)
    (hPartite : C₀.IsPartiteOver D)
    (hBased : Partite.Induced.BasedOn A D C₀ α C₁) :
    RelStructure.LocallyTreeLike A B C₁.toRelStructure n := by
  rcases hBased with ⟨N, hN, ⟨iso⟩⟩
  have hCanonical :=
    canonicalStep_locallyTreeLike
      A B D C₀ α hA eAB n hn hD hC₀ hPartite N hN
  exact hCanonical.pullback_embedding iso.toRelEmbedding

end StructuralRamsey.Partite.Iterated

namespace StructuralRamsey.Partite.Induced.Trace

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- Local tree-likeness propagates along the actual heterogeneous trace
returned by the induced partite construction. -/
theorem locallyTreeLike
    {A : RelStructure L U} {B : RelStructure L V}
    {D : RelStructure L P}
    {S T : Partite.Induced.Stage B D}
    {xs : List (Partite.Induced.RelevantEmbedding A B D)}
    (hTrace : Partite.Induced.Trace A B D S xs T)
    [Finite U] [Finite V] [Finite P]
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    (hS : RelStructure.LocallyTreeLike A B S.system.toRelStructure n) :
    RelStructure.LocallyTreeLike A B T.system.toRelStructure n := by
  induction hTrace with
  | nil =>
      exact hS
  | @snoc T R xs h α hBased ih =>
      exact Partite.Iterated.basedStep_locallyTreeLike
        A B D T.system α.1 R.system
        hA eAB n hn hD ih T.isPartite hBased

end StructuralRamsey.Partite.Induced.Trace

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- The concrete output of \`inducedConstruction\` is locally tree-like under
the hereditary-irreducibility hypothesis used by the checked step theorem. -/
theorem inducedConstruction_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B D κ)
    (hA : A.HereditarilyIrreducible)
    (eAB : RelStructure.Embedding A B)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1)) :
    letI : Nonempty (RelStructure.Embedding B D) :=
      nonempty_embedding_of_arrow A B D κ hRamsey
    let S₀ := initialStage B D
    ∃ T : Stage B D,
      Trace A B D S₀ (allRelevant A B D).reverse T ∧
      StructuralRamsey.Arrow A B T.system.toRelStructure κ ∧
      RelStructure.LocallyTreeLike A B T.system.toRelStructure n := by
  classical
  letI : Nonempty (RelStructure.Embedding B D) :=
    nonempty_embedding_of_arrow A B D κ hRamsey
  let S₀ := initialStage B D
  obtain ⟨T, hTrace, hArrow⟩ :=
    inducedConstruction A B D κ hRamsey
  have hInitial :
      RelStructure.LocallyTreeLike A B S₀.system.toRelStructure n := by
    exact Partite.Iterated.initial_locallyTreeLike
      A B
      (fun β : RelStructure.Embedding B D => β.toFunctionEmbedding)
      hA.irreducible n
  have hLocal :
      RelStructure.LocallyTreeLike A B T.system.toRelStructure n :=
    hTrace.locallyTreeLike hA eAB n hn hD hInitial
  exact ⟨T, hTrace, hArrow, hLocal⟩

end StructuralRamsey.Partite.Induced
