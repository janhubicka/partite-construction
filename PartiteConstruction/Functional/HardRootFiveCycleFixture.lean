import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Iterated.LooseStrictificationObstruction

/-!
# Finite maximal mixed hard-root test: literal old/core graph carriers

This file begins the exact Lean encoding of the ordinary-graph C5
obstruction to the over-uniform `MaximalMixedHardRootSchemaFromTwo`.
Both source sides and the selected support are REAL finite relational
structures, not informal lists of edges.

Old has vertices a0,b4,b2,a3,u0,u3 (Fin 6) and edges
a0--b4--b2--a3, u0--u3.
Core has c0,d1,c3,w0,w3 (Fin 5) and edges
c0--d1--c3, w0--w3.
The labels are, respectively, 0,4,2,3,0,3 and 0,1,3,0,3.

Selected A=K2 on labels 0,3; its complete support in Old
is {a0,a3,u0,u3}, an independent pair and a separate edge.
The full embedding into Core sends these four vertices to
c0,c3,w0,w3. Taking the exact free amalgam then creates C5
on the union of c0,d1,c3,b2,b4.

The standalone finite graphs and support embedding are
Lean-certified here. Their full EHN Stage/rank witness and
tree noncompletion consequences are developed in subsequent
modules: declaring those unproved here would defeat the audit.
-/

namespace StructuralRamsey.RelStructure.LooseNotStrictifiable.HardRootC5

open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.LooseNotStrictifiable

def oldPart : Fin 6 → Fin 5
  | 0 => 0
  | 1 => 4
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 3

def corePart : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 0
  | 4 => 3

def oldEdges : List (Fin 6 × Fin 6) :=
  [(0, 1), (1, 2), (2, 3), (4, 5)]

def coreEdges : List (Fin 5 × Fin 5) :=
  [(0, 1), (1, 2), (3, 4)]

def oldAdjacent (a b : Fin 6) : Prop :=
  (a, b) ∈ oldEdges ∨ (b, a) ∈ oldEdges

def coreAdjacent (a b : Fin 5) : Prop :=
  (a, b) ∈ coreEdges ∨ (b, a) ∈ coreEdges

def oldGraph : RelStructure L (Fin 6) where
  rel := fun _ x => oldAdjacent (x i0) (x i1)

def coreGraph : RelStructure L (Fin 5) where
  rel := fun _ x => coreAdjacent (x i0) (x i1)

/-- Support is the literal inverse image of the selected control
edge on parts 0 and 3; here every subset is closed, since there
are no function symbols. -/
def selected (x : Fin 6) : Prop :=
  x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5

/-- The explicitly listed four selected vertices are exactly
the inverse image of the A-part support {0,3}. -/
theorem selected_iff_parts (x : Fin 6) :
    selected x ↔ oldPart x = 0 ∨ oldPart x = 3 := by
  fin_cases x <;> norm_num [selected, oldPart]


def oldSelected := oldGraph.induce selected

/-- The embedding has two distinct vertices on part 0 and two
distinct vertices on part 3. Preserving the full induced graph,
not just edges, is essential for a native EHN support attachment. -/
def selectedMap (x : {a : Fin 6 // selected a}) : Fin 5 :=
  if x.1 = 0 then 0
  else if x.1 = 3 then 2
  else if x.1 = 4 then 3
  else 4

theorem selectedMap_injective : Function.Injective selectedMap := by
  intro x y hxy
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5 at hx
  change y = 0 ∨ y = 3 ∨ y = 4 ∨ y = 5 at hy
  rcases hx with (rfl | rfl | rfl | rfl) <;>
    rcases hy with (rfl | rfl | rfl | rfl) <;>
    simp_all [selectedMap]

theorem selectedMap_part (x : {a : Fin 6 // selected a}) :
    corePart (selectedMap x) = oldPart x.1 := by
  rcases x with ⟨x, hx⟩
  change x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5 at hx
  rcases hx with (rfl | rfl | rfl | rfl) <;>
    simp_all [selectedMap, oldPart, corePart]

theorem selectedMap_rel (x y : {a : Fin 6 // selected a}) :
    coreAdjacent (selectedMap x) (selectedMap y) ↔
      oldAdjacent x.1 y.1 := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5 at hx
  change y = 0 ∨ y = 3 ∨ y = 4 ∨ y = 5 at hy
  rcases hx with (rfl | rfl | rfl | rfl) <;>
    rcases hy with (rfl | rfl | rfl | rfl) <;>
    simp_all [selectedMap, oldAdjacent, coreAdjacent, oldEdges, coreEdges]

def selectedEmbedding : Embedding oldSelected coreGraph where
  toFun := selectedMap
  injective := selectedMap_injective
  map_rel_iff := by
    intro R x
    change coreAdjacent (selectedMap (x i0)) (selectedMap (x i1)) ↔
      oldAdjacent (x i0).1 (x i1).1
    exact selectedMap_rel (x i0) (x i1)

/-- A native binary free attachment of the literal Old and Core
graph carriers along the COMPLETE selected support. In the
function-free specialization the same vertex identification is
used by UnitAttachD. -/
noncomputable abbrev joined :=
  FreeAmalgam.amalgam oldSelected coreGraph oldGraph
    selectedEmbedding (inclusion oldGraph selected)

noncomputable def coreInto : Embedding coreGraph joined :=
  FreeAmalgam.leftEmbedding oldSelected coreGraph oldGraph
    selectedEmbedding (inclusion oldGraph selected)

noncomputable def oldInto : Embedding oldGraph joined :=
  FreeAmalgam.rightEmbedding oldSelected coreGraph oldGraph
    selectedEmbedding (inclusion oldGraph selected)

theorem overlap_at_a0 : coreInto 0 = oldInto 0 := by
  have h : selected (0 : Fin 6) := by
    simp [selected, oldPart]
  exact FreeAmalgam.left_right_overlap
    oldSelected coreGraph oldGraph
    selectedEmbedding (inclusion oldGraph selected)
    (⟨0, h⟩ : {a : Fin 6 // selected a})

theorem overlap_at_a3 : coreInto 2 = oldInto 3 := by
  have h : selected (3 : Fin 6) := by
    simp [selected, oldPart]
  exact FreeAmalgam.left_right_overlap
    oldSelected coreGraph oldGraph
    selectedEmbedding (inclusion oldGraph selected)
    (⟨3, h⟩ : {a : Fin 6 // selected a})

/-- Its five distinguished test vertices in cyclic order:
c0,d1,c3,b2,b4. The first three are in Core, the last two
come from the copied Old side. -/
noncomputable def cycleMap : Fin 5 → FreeAmalgam.Vertex
    oldSelected coreGraph oldGraph selectedEmbedding
      (inclusion oldGraph selected)
  | 0 => coreInto 0
  | 1 => coreInto 1
  | 2 => coreInto 2
  | 3 => oldInto 2
  | 4 => oldInto 1

end StructuralRamsey.RelStructure.LooseNotStrictifiable.HardRootC5
