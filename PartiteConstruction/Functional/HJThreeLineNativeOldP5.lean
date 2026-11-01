import PartiteConstruction.Functional.HJThreeLineC7NativeCore
import PartiteConstruction.Functional.Attachment

/-!
# Track D: actual old P5 functional-partite stage and its selected A-support

The original old P5 is a five-vertex strict edge-tree:
  a1 -- a0 -- c -- b1 -- b0.
Its selected A-part support is the four vertices a0,a1,b0,b1,
forming exactly two disjoint full A=K2 copies.

This is genuine native `FunctionalPartite.System` data over a
three-part control, with transversal relation tuples and no
function symbols. The selected support is function-closed,
and admits a FULL embedding into the two-letter selected system
from HJThreeLineC7NativeCore. Each of its genuine Hales--Jewett
line embeddings into the tagged coordinatewise power therefore
gives a FULL support attachment map preserving all three part
labels. No graph-only surrogate or phantom support is used.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

/-- Labels for the two A-parts of the actual old P5. -/
def label : Bool ↪ Fin 3 where
  toFun p := if p = false then 0 else 1
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- Old vertices: 0=a0, 1=a1, 2=b0, 3=b1, 4=c. -/
def oldPart (x : Fin 5) : Fin 3 :=
  if x = 0 ∨ x = 2 then 0 else
  if x = 1 ∨ x = 3 then 1 else 2

def oldEdge (x y : Fin 5) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
  (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
  (x = 0 ∧ y = 4) ∨ (x = 4 ∧ y = 0) ∨
  (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3)

/-- Every actual old P5 relation tuple is part transversal. -/
theorem oldEdge_distinct_parts (x y : Fin 5) (h : oldEdge x y) :
    oldPart x ≠ oldPart y := by
  fin_cases x <;> fin_cases y <;> simp_all [oldPart, oldEdge]

/-- Full partite old P5, with only the four old forest edges. -/
def oldSystem : FunctionalPartite.System Lang (Fin 3) (Fin 5) where
  toStructure := {
    rel Rel xs := by
      cases Rel
      change (Fin 2 → Fin 5) at xs
      exact oldEdge (xs 0) (xs 1)
    func F := Empty.elim F
  }
  part := oldPart
  relTransversal := by
    intro Rel xs hx i j hp
    cases Rel
    change (Fin 2 → Fin 5) at xs
    change Fin 2 at i
    change Fin 2 at j
    change oldEdge (xs 0) (xs 1) at hx
    have hne := oldEdge_distinct_parts (xs 0) (xs 1) hx
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne hp).elim
    · exact (hne hp.symm).elim
    · rfl
  funcTransversal := by
    intro F
    exact Empty.elim F

/-- Exact selected old support; the unique bridge is excluded. -/
def support : Set (Fin 5) := {x | x ≠ 4}

theorem support_closed : oldSystem.toStructure.IsClosed support := by
  intro F
  exact Empty.elim F

/-- Full old support to the two-letter genuine native selected system.
The letter component is a/b; the first component is the selected
A-part, and all four old support vertices are retained exactly. -/
def decode (x : support) : Bool × Bool :=
  if x.1 = 0 then (false, false) else
  if x.1 = 1 then (true, false) else
  if x.1 = 2 then (false, true) else (true, true)

theorem decode_injective : Function.Injective decode := by
  intro x y h
  apply Subtype.ext
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  fin_cases x <;> fin_cases y <;> simp_all [decode, support]

theorem support_rel_iff (x y : support) :
    R.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then decode x else decode y) ↔
    oldSystem.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then x.1 else y.1) := by
  change (decode x).1 ≠ (decode y).1 ∧
    (decode x).2 = (decode y).2 ↔ oldEdge x.1 y.1
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  fin_cases x <;> fin_cases y <;>
    simp_all [decode, support, oldEdge]

theorem support_part (x : support) :
    label (R.part (decode x)) = oldPart x.1 := by
  rcases x with ⟨x,hx⟩
  fin_cases x <;> simp_all [decode, support, R, label, oldPart]

/-- The old selected support is a FULL native substructure of R,
not a weakly completed or clipped graph. -/
def selectedFull : Structure.Embedding
    (oldSystem.induce support support_closed).toStructure
    R.toStructure where
  toFun := decode
  injective := decode_injective
  map_rel_iff := by
    intro Rel xs
    cases Rel
    exact support_rel_iff (xs 0) (xs 1)
  map_func := by
    intro F
    exact Empty.elim F

/-- The same old support embeds FULLY along any genuine HJ line
into the true two-letter native power, with part labels relabelled
into the original three-part control. -/
def selectedLine (W : StructuralRamsey.HalesJewett.Line
    (Induced.Letter A R) 2) :
    FunctionalPartite.Embedding
      (oldSystem.induce support support_closed)
      ((Induced.power R 2).relabel label) where
  toEmbedding :=
    (Induced.weak_lineEmbedding R_weakProjection W).toEmbedding.comp
      selectedFull
  map_part := by
    intro x
    change label (R.part (decode x)) = oldPart x.1
    exact support_part x

/-- The line index is an actual finite family of three full support
embeddings, not a mere choice of three graph homomorphisms. -/
def chosenLine : Fin 3 →
    StructuralRamsey.HalesJewett.Line (Induced.Letter A R) 2
  | 0 => W0
  | 1 => W1
  | _ => W2

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7
