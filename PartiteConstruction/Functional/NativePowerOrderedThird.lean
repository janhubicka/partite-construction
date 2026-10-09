import PartiteConstruction.Functional.NativePowerOrderedSource

/-! # A seven-vertex strict EHN tree over a hereditarily irreducible base

Attach the ordered third B-copy over the singleton X-root of the
previously verified ordered five-vertex stage. The only new order
tuples are those inherited from that third full B-copy.

The result is the original seven-vertex native Hales--Jewett input,
with precisely the same function fibres and part map, now in the
expanded language with a pairwise order on B. The next proof stage
will address the power and its bounded closed obstruction.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- The union of all order tuples from the first two B-copies
and the last B-copy. -/
def oldStageOrder (a b : Fin 7) : Prop :=
  (∃ i j : Fin 5, firstStageOrder i j ∧
    a = firstIntoOldMap i ∧ b = firstIntoOldMap j) ∨
  (∃ i j : Fin 3, i < j ∧
    a = thirdCopyMap i ∧ b = thirdCopyMap j)

instance oldStageOrderDecidable (a b : Fin 7) :
    Decidable (oldStageOrder a b) := by
  unfold oldStageOrder
  infer_instance

def oldStageOrdered : Structure toyLanguage.withLinearOrder (Fin 7) where
  rel R := by
    cases R with
    | inl r => exact oldStage.rel r
    | inr _ => exact fun (x : Fin 2 → Fin 7) =>
        oldStageOrder (x 0) (x 1)
  func := oldStage.func

theorem oldStageOrder_firstIntoOld :
    ∀ i j : Fin 5,
      oldStageOrder (firstIntoOldMap i) (firstIntoOldMap j) ↔
        firstStageOrder i j := by
  decide

theorem oldStageOrder_thirdCopy :
    ∀ i j : Fin 3,
      oldStageOrder (thirdCopyMap i) (thirdCopyMap j) ↔ i < j := by
  decide

def firstIntoOldOrdered :
    Embedding firstStageOrdered oldStageOrdered where
  toFun := firstIntoOldMap
  injective := firstIntoOld.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact firstIntoOld.map_rel_iff R x
    | inr u =>
        cases u
        change (Fin 2 → Fin 5) at x
        change oldStageOrder (firstIntoOldMap (x 0))
          (firstIntoOldMap (x 1)) ↔ firstStageOrder (x 0) (x 1)
        exact oldStageOrder_firstIntoOld (x 0) (x 1)
  map_func := firstIntoOld.map_func

def thirdCopyOrdered : Embedding toyBaseOrdered oldStageOrdered where
  toFun := thirdCopyMap
  injective := thirdCopy.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact thirdCopy.map_rel_iff R x
    | inr u =>
        cases u
        change (Fin 2 → Fin 3) at x
        change oldStageOrder (thirdCopyMap (x 0))
          (thirdCopyMap (x 1)) ↔ x 0 < x 1
        exact oldStageOrder_thirdCopy (x 0) (x 1)
  map_func := thirdCopy.map_func

/-- Closed X-root, with no relation in the added order symbol. -/
def xRootOrdered : Structure toyLanguage.withLinearOrder Unit where
  rel R := by
    cases R with
    | inl r => exact xRoot.rel r
    | inr _ => exact fun (_ : Fin 2 → Unit) => False
  func := xRoot.func

def xRootFirstOrdered :
    Embedding xRootOrdered firstStageOrdered where
  toFun := xRootFirst
  injective := xRootFirst.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact xRootFirst.map_rel_iff R x
    | inr _ =>
        change firstStageOrder (1 : Fin 5) 1 ↔ False
        decide
  map_func := xRootFirst.map_func

def xRootBaseOrdered : Embedding xRootOrdered toyBaseOrdered where
  toFun := xRootBase
  injective := xRootBase.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact xRootBase.map_rel_iff R x
    | inr _ =>
        change ((0 : Fin 3) < 0) ↔ False
        simp
  map_func := xRootBase.map_func

theorem xRootFirstOrdered_contained :
    xRootFirstOrdered.ContainedInIrreducible := by
  refine ⟨Fin 3,toyBaseOrdered,toyBaseOrdered_irreducible,
    secondCopyOrdered,?_⟩
  intro _
  exact ⟨0,rfl⟩

theorem xRootBaseOrdered_contained :
    xRootBaseOrdered.ContainedInIrreducible := by
  refine ⟨Fin 3,toyBaseOrdered,toyBaseOrdered_irreducible,
    Embedding.id toyBaseOrdered,?_⟩
  intro _
  exact ⟨0,rfl⟩

/-- The new order relation is exactly the free union of the two
constituents' order relations. -/
theorem oldStageOrder_free_iff :
    ∀ x : Fin 2 → Fin 7,
      oldStageOrder (x 0) (x 1) ↔
      (∃ a : Fin 2 → Fin 5,
          firstStageOrder (a 0) (a 1) ∧
          x = firstIntoOldMap ∘ a) ∨
      (∃ a : Fin 2 → Fin 3,
          a 0 < a 1 ∧ x = thirdCopyMap ∘ a) := by
  decide

theorem oldStageOrdered_free :
    IsFreeAmalgam xRootFirstOrdered xRootBaseOrdered
      firstIntoOldOrdered thirdCopyOrdered := by
  constructor
  · exact oldStage_free.covers
  · exact oldStage_free.overlap
  · intro R x
    cases R with
    | inl R => exact oldStage_free.rel_iff R x
    | inr u =>
        cases u
        change (Fin 2 → Fin 7) at x
        change oldStageOrder (x 0) (x 1) ↔
          (∃ a : Fin 2 → Fin 5,
              firstStageOrder (a 0) (a 1) ∧
              x = firstIntoOldMap ∘ a) ∨
          (∃ a : Fin 2 → Fin 3,
              a 0 < a 1 ∧ x = thirdCopyMap ∘ a)
        exact oldStageOrder_free_iff x
  · exact oldStage_free.func_iff

/-- The ordered seven-vertex input is a strict full-functional B-tree. -/
theorem oldStageOrdered_strictTree :
    TreeAmalgam toyBaseOrdered (Fin 7) oldStageOrdered := by
  exact TreeAmalgam.glue
    firstStageOrdered_strictTree
    (TreeAmalgam.copy (Embedding.id toyBaseOrdered)
      (fun b => ⟨b,rfl⟩))
    xRootFirstOrdered xRootBaseOrdered
    xRootFirstOrdered_contained xRootBaseOrdered_contained
    firstIntoOldOrdered thirdCopyOrdered oldStageOrdered_free

/-- Its part map remains weak EHN and full on every irreducible
closed source piece. -/
theorem oldStageOrdered_projection :
    oldStageOrdered.IsEHNHomomorphismEmbedding toyBaseOrdered oldPart := by
  apply IsEHNHomomorphismEmbedding.of_freeAmalgam
    oldStageOrdered_free firstStageOrdered_projection
    (Embedding.id toyBaseOrdered).isEHNHomomorphismEmbedding
  · intro x
    exact firstIntoOldMap_part x
  · intro x
    exact thirdCopyMap_part x

theorem oldStageOrdered_reduct :
    oldStageOrdered.linearOrderReduct = oldStage := rfl

end StructuralRamsey.Structure.NativePowerObstruction
