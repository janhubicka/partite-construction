import PartiteConstruction.Functional.NativePowerFullObstruction
import PartiteConstruction.Functional.WeakAttachment
import PartiteConstruction.Functional.DirectWeakIteration

/-! # The input stage of the native-power obstruction is a genuine full B-tree

The old seven-vertex input stage consists of three full-function copies of
the three-vertex base:
  B0 = {x0,y0,z00}, B1 = {x1,y0,z10}, B2 = {x1,y1,z11}.
First amalgamate B0 and B1 over the function-closed singleton {y0};
then attach B2 over the function-closed singleton {x1}.

This establishes that the native power counterexample starts from a bona
fide strict full-functional B-tree, rather than merely an arbitrary
weakly-partite function structure. Weak projections into the same base
are glued using the established EHN free-amalgam lemma.

The test and its projected image stay *weak* in the vertex-size induction;
nothing here replaces projected images by their function-closed hulls.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

/-- A two-edge functional tree: x0--y0 and x1--y0, with distinct outputs. -/
def firstStagePart (z : Fin 5) : Fin 3 :=
  if z.val < 2 then 0 else if z = 2 then 1 else 2

def firstStageOutput (x y : Fin 5) : Option (Fin 5) :=
  if x = 0 ∧ y = 2 then some 3
  else if x = 1 ∧ y = 2 then some 4
  else none

def firstStage : Structure toyLanguage (Fin 5) where
  rel R x := firstStagePart (x (0 : Fin 1)) = R
  func _ x := {y |
    firstStageOutput (x (0 : Fin 2)) (x (1 : Fin 2)) = some y}

/-- Explicit vertex maps for two full copies of the template. -/
def firstCopyMap (i : Fin 3) : Fin 5 :=
  if i = 0 then 0 else if i = 1 then 2 else 3

def secondCopyMap (i : Fin 3) : Fin 5 :=
  if i = 0 then 1 else if i = 1 then 2 else 4

theorem firstCopyMap_part (i : Fin 3) :
    firstStagePart (firstCopyMap i) = i := by
  fin_cases i <;> decide

theorem secondCopyMap_part (i : Fin 3) :
    firstStagePart (secondCopyMap i) = i := by
  fin_cases i <;> decide

/-- Full embeddings of the first and second base copies into the two-edge stage. -/
def firstCopy : Embedding toyBase firstStage where
  toFun := firstCopyMap
  injective := by decide
  map_rel_iff := by
    intro R x
    change firstStagePart (firstCopyMap (x (0 : Fin 1))) = R ↔
      x (0 : Fin 1) = R
    rw [firstCopyMap_part]
  map_func := by
    intro F x
    ext y
    change (∃ z : Fin 3,
        (x (0 : Fin 2) = 0 ∧ x (1 : Fin 2) = 1 ∧ z = 2) ∧
          firstCopyMap z = y) ↔
      firstStageOutput (firstCopyMap (x (0 : Fin 2)))
        (firstCopyMap (x (1 : Fin 2))) = some y
    generalize h₀ : x (0 : Fin 2) = a
    generalize h₁ : x (1 : Fin 2) = b
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

def secondCopy : Embedding toyBase firstStage where
  toFun := secondCopyMap
  injective := by decide
  map_rel_iff := by
    intro R x
    change firstStagePart (secondCopyMap (x (0 : Fin 1))) = R ↔
      x (0 : Fin 1) = R
    rw [secondCopyMap_part]
  map_func := by
    intro F x
    ext y
    change (∃ z : Fin 3,
        (x (0 : Fin 2) = 0 ∧ x (1 : Fin 2) = 1 ∧ z = 2) ∧
          secondCopyMap z = y) ↔
      firstStageOutput (secondCopyMap (x (0 : Fin 2)))
        (secondCopyMap (x (1 : Fin 2))) = some y
    generalize h₀ : x (0 : Fin 2) = a
    generalize h₁ : x (1 : Fin 2) = b
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

/-- The Y-vertex singleton has no defined binary function values. -/
def yRoot : Structure toyLanguage Unit where
  rel R _ := R = (1 : Fin 3)
  func _ _ := ∅

def yRootBase : Embedding yRoot toyBase where
  toFun _ := 1
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := by
    intro R x
    change (1 : Fin 3) = R ↔ R = (1 : Fin 3)
    exact eq_comm
  map_func := by
    intro F x
    ext y
    change (∃ z : Unit, False ∧ (1 : Fin 3) = y) ↔
      ((1 : Fin 3) = 0 ∧ (1 : Fin 3) = 1 ∧ y = 2)
    simp

/-- The three-vertex base is irreducible in the full function language. -/
theorem toyBase_irreducible : toyBase.Irreducible := by
  apply irreducible_of_graph_irreducible toyBase
  intro a b hab
  refine ⟨.inr (), (fun i : Fin 3 => i), a, b, ?_, rfl, rfl⟩
  change (2 : Fin 3) ∈ toyBase.func () ![0, 1]
  change (0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1 ∧ (2 : Fin 3) = 2
  exact ⟨rfl, rfl, rfl⟩

theorem yRootBase_contained :
    yRootBase.ContainedInIrreducible := by
  refine ⟨Fin 3, toyBase, toyBase_irreducible,
    Embedding.id toyBase, ?_⟩
  intro _
  exact ⟨1, rfl⟩

/-- The first two edges form an exact full functional free amalgam. -/
theorem firstStage_free :
    IsFreeAmalgam yRootBase yRootBase firstCopy secondCopy := by
  constructor
  · intro z
    fin_cases z <;> decide
  · intro a b
    fin_cases a <;> fin_cases b <;> decide
  · change ∀ (R : Fin 3) (x : Fin 1 → Fin 5),
        (firstStagePart (x 0) = R) ↔
        (∃ a : Fin 1 → Fin 3,
          a 0 = R ∧ x = firstCopyMap ∘ a) ∨
        (∃ a : Fin 1 → Fin 3,
          a 0 = R ∧ x = secondCopyMap ∘ a)
    decide
  · change ∀ (_F : Unit) (x : Fin 2 → Fin 5) (y : Fin 5),
        (firstStageOutput (x 0) (x 1) = some y) ↔
        (∃ a : Fin 2 → Fin 3, ∃ b : Fin 3,
          (a 0 = 0 ∧ a 1 = 1 ∧ b = 2) ∧
          x = firstCopyMap ∘ a ∧ y = firstCopyMap b) ∨
        (∃ a : Fin 2 → Fin 3, ∃ b : Fin 3,
          (a 0 = 0 ∧ a 1 = 1 ∧ b = 2) ∧
          x = secondCopyMap ∘ a ∧ y = secondCopyMap b)
    intro F x y
    have hx : x = ![x (0 : Fin 2), x (1 : Fin 2)] := by
      funext i
      fin_cases i <;> rfl
    generalize h₀ : x (0 : Fin 2) = a at hx ⊢
    generalize h₁ : x (1 : Fin 2) = b at hx ⊢
    rw [hx]
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

theorem firstStage_strictTree :
    TreeAmalgam toyBase (Fin 5) firstStage := by
  exact TreeAmalgam.glue
    (TreeAmalgam.copy (Embedding.id toyBase) (fun b => ⟨b, rfl⟩))
    (TreeAmalgam.copy (Embedding.id toyBase) (fun b => ⟨b, rfl⟩))
    yRootBase yRootBase yRootBase_contained yRootBase_contained
    firstCopy secondCopy firstStage_free

/-- Projection of the two-edge stage to the three-vertex base. -/
theorem firstStage_projection :
    firstStage.IsEHNHomomorphismEmbedding toyBase firstStagePart := by
  apply IsEHNHomomorphismEmbedding.of_freeAmalgam
    firstStage_free
    (Embedding.id toyBase).isEHNHomomorphismEmbedding
    (Embedding.id toyBase).isEHNHomomorphismEmbedding
  · intro x
    fin_cases x <;> decide
  · intro x
    fin_cases x <;> decide


/-- The actual seven-vertex stage is the full amalgam of `firstStage`
and one more B-copy, attached over their shared X-vertex. -/
def firstIntoOldMap (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2
  else if i = 3 then 4 else 5

def thirdCopyMap (i : Fin 3) : Fin 7 :=
  if i = 0 then 1 else if i = 1 then 3 else 6

theorem firstIntoOldMap_part (i : Fin 5) :
    oldPart (firstIntoOldMap i) = firstStagePart i := by
  fin_cases i <;> decide

theorem thirdCopyMap_part (i : Fin 3) :
    oldPart (thirdCopyMap i) = i := by
  fin_cases i <;> decide

def firstIntoOld : Embedding firstStage oldStage where
  toFun := firstIntoOldMap
  injective := by decide
  map_rel_iff := by
    intro R x
    change oldPart (firstIntoOldMap (x (0 : Fin 1))) = R ↔
      firstStagePart (x (0 : Fin 1)) = R
    rw [firstIntoOldMap_part]
  map_func := by
    intro F x
    ext y
    change (∃ z : Fin 5,
        firstStageOutput (x (0 : Fin 2)) (x (1 : Fin 2)) = some z ∧
        firstIntoOldMap z = y) ↔
      oldOutput (firstIntoOldMap (x (0 : Fin 2)))
        (firstIntoOldMap (x (1 : Fin 2))) = some y
    generalize h₀ : x (0 : Fin 2) = a
    generalize h₁ : x (1 : Fin 2) = b
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

def thirdCopy : Embedding toyBase oldStage where
  toFun := thirdCopyMap
  injective := by decide
  map_rel_iff := by
    intro R x
    change oldPart (thirdCopyMap (x (0 : Fin 1))) = R ↔
      x (0 : Fin 1) = R
    rw [thirdCopyMap_part]
  map_func := by
    intro F x
    ext y
    change (∃ z : Fin 3,
        (x (0 : Fin 2) = 0 ∧ x (1 : Fin 2) = 1 ∧ z = 2) ∧
        thirdCopyMap z = y) ↔
      oldOutput (thirdCopyMap (x (0 : Fin 2)))
        (thirdCopyMap (x (1 : Fin 2))) = some y
    generalize h₀ : x (0 : Fin 2) = a
    generalize h₁ : x (1 : Fin 2) = b
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

/-- The third attachment has the closed one-vertex X-root. -/
def xRoot : Structure toyLanguage Unit where
  rel R _ := R = (0 : Fin 3)
  func _ _ := ∅

def xRootFirst : Embedding xRoot firstStage where
  toFun _ := 1
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := by
    intro R x
    change (0 : Fin 3) = R ↔ R = (0 : Fin 3)
    exact eq_comm
  map_func := by
    intro F x
    ext y
    change (∃ z : Unit, False ∧ (1 : Fin 5) = y) ↔
      firstStageOutput 1 1 = some y
    fin_cases y <;> decide

def xRootBase : Embedding xRoot toyBase where
  toFun _ := 0
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := by
    intro R x
    change (0 : Fin 3) = R ↔ R = (0 : Fin 3)
    exact eq_comm
  map_func := by
    intro F x
    ext y
    change (∃ z : Unit, False ∧ (0 : Fin 3) = y) ↔
      ((0 : Fin 3) = 0 ∧ (0 : Fin 3) = 1 ∧ y = 2)
    simp

theorem xRootFirst_contained :
    xRootFirst.ContainedInIrreducible := by
  refine ⟨Fin 3, toyBase, toyBase_irreducible, secondCopy, ?_⟩
  intro _
  exact ⟨0, rfl⟩

theorem xRootBase_contained :
    xRootBase.ContainedInIrreducible := by
  refine ⟨Fin 3, toyBase, toyBase_irreducible,
    Embedding.id toyBase, ?_⟩
  intro _
  exact ⟨0, rfl⟩

/-- This is the exact full-function free-amalgam decomposition of the
concrete input of the native Hales--Jewett power. -/
theorem oldStage_free :
    IsFreeAmalgam xRootFirst xRootBase firstIntoOld thirdCopy := by
  constructor
  · intro z
    fin_cases z <;> decide
  · intro a b
    fin_cases a <;> fin_cases b <;> decide
  · change ∀ (R : Fin 3) (x : Fin 1 → Fin 7),
        (oldPart (x 0) = R) ↔
        (∃ a : Fin 1 → Fin 5,
          firstStagePart (a 0) = R ∧ x = firstIntoOldMap ∘ a) ∨
        (∃ a : Fin 1 → Fin 3,
          a 0 = R ∧ x = thirdCopyMap ∘ a)
    decide
  · change ∀ (_F : Unit) (x : Fin 2 → Fin 7) (y : Fin 7),
        (oldOutput (x 0) (x 1) = some y) ↔
        (∃ a : Fin 2 → Fin 5, ∃ b : Fin 5,
          (firstStageOutput (a 0) (a 1) = some b) ∧
          x = firstIntoOldMap ∘ a ∧ y = firstIntoOldMap b) ∨
        (∃ a : Fin 2 → Fin 3, ∃ b : Fin 3,
          (a 0 = 0 ∧ a 1 = 1 ∧ b = 2) ∧
          x = thirdCopyMap ∘ a ∧ y = thirdCopyMap b)
    intro _F x y
    have hx : x = ![x (0 : Fin 2), x (1 : Fin 2)] := by
      funext i
      fin_cases i <;> rfl
    generalize h₀ : x (0 : Fin 2) = a at hx ⊢
    generalize h₁ : x (1 : Fin 2) = b at hx ⊢
    rw [hx]
    fin_cases a <;> fin_cases b <;> fin_cases y <;> decide

/-- The seven-vertex input of the native power is *itself* a strict
full-function B-tree, not just a weak graph-tree. -/
theorem oldStage_strictTree :
    TreeAmalgam toyBase (Fin 7) oldStage := by
  exact TreeAmalgam.glue
    firstStage_strictTree
    (TreeAmalgam.copy (Embedding.id toyBase) (fun b => ⟨b, rfl⟩))
    xRootFirst xRootBase xRootFirst_contained xRootBase_contained
    firstIntoOld thirdCopy oldStage_free

/-- Its original part map is a genuine weak EHN homomorphism-embedding,
full on all irreducible closed tests, despite failure of global
function-domain reflection. -/
theorem oldStage_projection :
    oldStage.IsEHNHomomorphismEmbedding toyBase oldPart := by
  apply IsEHNHomomorphismEmbedding.of_freeAmalgam
    oldStage_free firstStage_projection
    (Embedding.id toyBase).isEHNHomomorphismEmbedding
  · intro x
    exact firstIntoOldMap_part x
  · intro x
    exact thirdCopyMap_part x

theorem oldSystem_weaklyPartiteOver :
    oldSystem.WeaklyPartiteOver toyBase :=
  oldStage_projection

theorem actualPower_weaklyPartiteOver :
    (FunctionalPartite.Induced.power oldSystem 2).WeaklyPartiteOver
      toyBase :=
  FunctionalPartite.Induced.power_weaklyPartiteOver
    oldSystem_weaklyPartiteOver (by omega)


end StructuralRamsey.Structure.NativePowerObstruction
