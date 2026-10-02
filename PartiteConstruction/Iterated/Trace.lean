import PartiteConstruction.Iterated.Based
import PartiteConstruction.Iterated.Initial
import PartiteConstruction.Partite.InducedConstruction

/-! # The tree invariant along an induced-construction trace

Each relevant successor carries its own factorization A -> B -> D, supplying
the A-to-B embedding needed in the power-core case.  The induction therefore
requires no global A-to-B hypothesis beyond the induced trace itself.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- Local tree-likeness propagates along any typed induced trace, assuming the
initial stage already has the desired invariant. -/
theorem trace_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : A.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    {S T : Partite.Induced.Stage B D}
    {xs : List (Partite.Induced.RelevantEmbedding A B D)}
    (hTrace : Partite.Induced.Trace A B D S xs T)
    (hS : RelStructure.LocallyTreeLike A B S.system.toRelStructure n) :
    RelStructure.LocallyTreeLike A B T.system.toRelStructure n := by
  induction hTrace with
  | nil =>
      exact hS
  | @snoc S T R xs h α hBased ih =>
      have hT :
          RelStructure.LocallyTreeLike A B T.system.toRelStructure n :=
        ih hS
      rcases α.2 with ⟨β, eAB, hfac⟩
      exact basedStep_locallyTreeLike
        A B D T.system R.system α.1
        hA eAB n hn hD hT T.isPartite hBased

/-- The sequence produced by the induced construction satisfies the
strengthened tree invariant whenever A is hereditarily irreducible. -/
theorem inducedTrace_locallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    [Nonempty (RelStructure.Embedding B D)]
    (hA : A.HereditarilyIrreducible)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A B D (n - 1))
    {T : Partite.Induced.Stage B D}
    {xs : List (Partite.Induced.RelevantEmbedding A B D)}
    (hTrace :
      Partite.Induced.Trace A B D
        (Partite.Induced.initialStage B D) xs T) :
    RelStructure.LocallyTreeLike A B T.system.toRelStructure n := by
  let β : RelStructure.Embedding B D → V ↪ P :=
    fun e => e.toFunctionEmbedding
  have hInitial :
      RelStructure.LocallyTreeLike A B
        (Partite.Induced.initialStage B D).system.toRelStructure n := by
    change RelStructure.LocallyTreeLike A B
      (Partite.Initial.picture B β).toRelStructure n
    exact initial_locallyTreeLike A B β hA.irreducible n
  exact trace_locallyTreeLike A B D hA n hn hD hTrace hInitial

end StructuralRamsey.Partite.Iterated
