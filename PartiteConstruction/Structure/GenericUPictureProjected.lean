import PartiteConstruction.Structure.GenericUOrdinaryClosedEmbedding
import PartiteConstruction.Structure.GenericUClosedPartiteArrow
import PartiteConstruction.Functional.ClosedPicture

/-!
# Track F — original projected closed copies for the Picture lemma

The original arbitrary-relational Picture lemma colours U-closed A-copies
of a D-partite system B whose part projection is a prescribed map alpha.
The verified graph-language Picture lemma uses ProjectedEmbedding with
closed graph embeddings. Neither alpha nor those copies are partite
embeddings themselves.

This module compares the exact projected-embedding TYPES on the literal
same vertex injections and part maps. It also verifies compatibility of
the actual original projection-preserving copy composition.

No Picture Ramsey theorem is claimed in this module.
-/

namespace StructuralRamsey.Partite.OriginalUClosed

universe u v

variable {L : RelLanguage.{u}} {P T V W : Type v}

/-- U-closed induced A-copies of an original relational P-partite system
whose named-part projection is the prescribed map alpha:T→P. -/
def ProjectedEmbedding
    (A : RelStructure L T)
    (B : Partite.System L P V)
    (α : T → P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) : Type _ :=
  {e : {f : RelStructure.Embedding A B.toRelStructure //
          RelStructure.IsUClosedEmbeddingRange U hU f} //
    ∀ x, B.part (e.1.1 x) = α x}

/-- The prescribed projection remains literally the same function when
every relation is reindexed to its unique nonredundant U-graph symbol. -/
noncomputable def projectedEmbeddingEquiv
    (A : RelStructure L T)
    (B : Partite.System L P V)
    (α : T → P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    ProjectedEmbedding A B α U hU ≃
      Partite.Closed.ProjectedEmbedding
        (A.asReducedUGraph U hU)
        (B.asReducedUGraph U hU) α where
  toFun e := by
    let E := RelStructure.Embedding.uClosedReducedGraphEquiv
      (A := A) (B := B.toRelStructure) U hU
    exact ⟨E e.1, e.2⟩
  invFun g := by
    let E := RelStructure.Embedding.uClosedReducedGraphEquiv
      (A := A) (B := B.toRelStructure) U hU
    exact ⟨E.symm g.1, g.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro g
    apply Partite.Closed.ProjectedEmbedding.ext
    intro x
    rfl

/-- Composition of a projected original A-copy with an original U-closed
partite B-copy remains projected and U-closed on the SAME map. -/
def ProjectedEmbedding.comp
    {A : RelStructure L T}
    {B : Partite.System L P V}
    {C : Partite.System L P W}
    (α : T → P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : ProjectedEmbedding A B α U hU)
    (f : Embedding B C U hU) :
    ProjectedEmbedding A C α U hU := by
  let fg : {g : RelStructure.Embedding B.toRelStructure
      C.toRelStructure // RelStructure.IsUClosedEmbeddingRange U hU g} :=
    ⟨f.1.toEmbedding, f.2⟩
  refine ⟨RelStructure.uClosedRangeComp U hU fg e.1, ?_⟩
  intro x
  exact (f.1.map_part (e.1.1 x)).trans (e.2 x)

/-- Projected copies commute with actual closed partite composition, not
just with an abstract isomorphism of embedding types. -/
theorem projectedEmbeddingEquiv_comp
    {A : RelStructure L T}
    {B : Partite.System L P V}
    {C : Partite.System L P W}
    (α : T → P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : ProjectedEmbedding A B α U hU)
    (f : Embedding B C U hU) :
    (projectedEmbeddingEquiv A C α U hU)
      (ProjectedEmbedding.comp α U hU e f) =
    Partite.Closed.ProjectedEmbedding.comp
      ((projectedEmbeddingEquiv A B α U hU) e)
      ((Partite.Embedding.uClosedReindexEquiv U hU) f) := by
  apply Partite.Closed.ProjectedEmbedding.ext
  intro x
  rfl

end StructuralRamsey.Partite.OriginalUClosed
