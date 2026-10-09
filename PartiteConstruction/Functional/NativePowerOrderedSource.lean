import PartiteConstruction.Functional.NativePowerOrderedTarget
import PartiteConstruction.Functional.NativePowerInputTree

/-! # Native functional power: hereditary-order source certificates

The hereditary-irreducible version of the native power obstruction
expands the three-vertex base by its binary strict order. Intermediate
stages carry only those order tuples inherited from their constituent
B-copies; adding a *global* linear order to the old stages would break
their full free-amalgam decomposition.

This module first constructs the ordered two-edge tree. The third edge
and its genuine tagged power are treated after this checkpoint.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The binary order tuples within the two original B-copies, with
no invented tuple joining vertices in different copies. -/
def firstStageOrder (a b : Fin 5) : Prop :=
  (∃ i j : Fin 3, i < j ∧
      a = firstCopyMap i ∧ b = firstCopyMap j) ∨
  (∃ i j : Fin 3, i < j ∧
      a = secondCopyMap i ∧ b = secondCopyMap j)

/-- Full functional structure on the *same five source vertices*,
expanding only the relation language. -/
def firstStageOrdered :
    Structure toyLanguage.withLinearOrder (Fin 5) where
  rel R z := match R with
    | .inl r => firstStage.rel r z
    | .inr _ => firstStageOrder (z 0) (z 1)
  func := firstStage.func

theorem firstStageOrder_firstCopy :
    ∀ i j : Fin 3,
      firstStageOrder (firstCopyMap i) (firstCopyMap j) ↔ i < j := by
  decide

theorem firstStageOrder_secondCopy :
    ∀ i j : Fin 3,
      firstStageOrder (secondCopyMap i) (secondCopyMap j) ↔ i < j := by
  decide

def firstCopyOrdered : Embedding toyBaseOrdered firstStageOrdered where
  toFun := firstCopyMap
  injective := firstCopy.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact firstCopy.map_rel_iff R x
    | inr _ =>
        change firstStageOrder (firstCopyMap (x 0))
            (firstCopyMap (x 1)) ↔ x 0 < x 1
        exact firstStageOrder_firstCopy (x 0) (x 1)
  map_func := firstCopy.map_func

def secondCopyOrdered : Embedding toyBaseOrdered firstStageOrdered where
  toFun := secondCopyMap
  injective := secondCopy.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact secondCopy.map_rel_iff R x
    | inr _ =>
        change firstStageOrder (secondCopyMap (x 0))
            (secondCopyMap (x 1)) ↔ x 0 < x 1
        exact firstStageOrder_secondCopy (x 0) (x 1)
  map_func := secondCopy.map_func

/-- The singleton Y-root has no order tuples and no function values. -/
def yRootOrdered : Structure toyLanguage.withLinearOrder Unit where
  rel R z := match R with
    | .inl r => yRoot.rel r z
    | .inr _ => False
  func := yRoot.func

def yRootBaseOrdered : Embedding yRootOrdered toyBaseOrdered where
  toFun := yRootBase
  injective := yRootBase.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact yRootBase.map_rel_iff R x
    | inr _ =>
        change ((1 : Fin 3) < 1) ↔ False
        simp
  map_func := yRootBase.map_func

theorem toyBaseOrdered_irreducible :
    toyBaseOrdered.Irreducible :=
  irreducible_of_graph_irreducible toyBaseOrdered
    toyBaseOrdered_graph_hereditarilyIrreducible.irreducible

theorem yRootBaseOrdered_contained :
    yRootBaseOrdered.ContainedInIrreducible := by
  refine ⟨Fin 3,toyBaseOrdered,toyBaseOrdered_irreducible,
      Embedding.id toyBaseOrdered,?_⟩
  intro _
  exact ⟨1,rfl⟩

/-- Finite verification of the newly introduced order tuples.
Each one belongs to one original constituent copy and vice versa. -/
theorem firstStageOrder_free_iff :
    ∀ x : Fin 2 → Fin 5,
      firstStageOrder (x 0) (x 1) ↔
      (∃ a : Fin 2 → Fin 3,
          a 0 < a 1 ∧ x = firstCopyMap ∘ a) ∨
      (∃ a : Fin 2 → Fin 3,
          a 0 < a 1 ∧ x = secondCopyMap ∘ a) := by
  decide

/-- The old full free amalgam remains full after adjoining only its
copy-local order relations. -/
theorem firstStageOrdered_free :
    IsFreeAmalgam yRootBaseOrdered yRootBaseOrdered
      firstCopyOrdered secondCopyOrdered := by
  constructor
  · exact firstStage_free.covers
  · exact firstStage_free.overlap
  · intro R x
    cases R with
    | inl R =>
        exact firstStage_free.rel_iff R x
    | inr _ =>
        change firstStageOrder (x 0) (x 1) ↔
          (∃ a : Fin 2 → Fin 3,
              a 0 < a 1 ∧ x = firstCopyMap ∘ a) ∨
          (∃ a : Fin 2 → Fin 3,
              a 0 < a 1 ∧ x = secondCopyMap ∘ a)
        exact firstStageOrder_free_iff x
  · exact firstStage_free.func_iff

theorem firstStageOrdered_strictTree :
    TreeAmalgam toyBaseOrdered (Fin 5) firstStageOrdered := by
  exact TreeAmalgam.glue
    (TreeAmalgam.copy (Embedding.id toyBaseOrdered)
      (fun a => ⟨a,rfl⟩))
    (TreeAmalgam.copy (Embedding.id toyBaseOrdered)
      (fun a => ⟨a,rfl⟩))
    yRootBaseOrdered yRootBaseOrdered
    yRootBaseOrdered_contained yRootBaseOrdered_contained
    firstCopyOrdered secondCopyOrdered firstStageOrdered_free

theorem firstStageOrdered_projection :
    firstStageOrdered.IsEHNHomomorphismEmbedding
      toyBaseOrdered firstStagePart := by
  apply IsEHNHomomorphismEmbedding.of_freeAmalgam
    firstStageOrdered_free
    (Embedding.id toyBaseOrdered).isEHNHomomorphismEmbedding
    (Embedding.id toyBaseOrdered).isEHNHomomorphismEmbedding
  · intro x
    exact firstCopyMap_part x
  · intro x
    exact secondCopyMap_part x

end StructuralRamsey.Structure.NativePowerObstruction
