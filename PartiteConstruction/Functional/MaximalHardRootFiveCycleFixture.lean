import PartiteConstruction.Functional.EHNAttachmentDecompose

/-!
# Finite genuine-function-language stages for the maximal mixed C5 audit

The arbitrary-stage `MaximalMixedHardRootSchemaFromTwo` from the
published-style strict functional sparsening library is refuted
mathematically by two forests meeting over an independent
two-generated separator, with a genuine five-cycle in their
full selected-support free attachment.

This file begins an exact kernel-checked encoding in the *native*
relation-and-function `Structure` / `FunctionalPartite.System`
language, rather than a standalone graph regression. There are NO
function symbols in this instance.

This first module records concrete carriers, relations, part labels,
the function-closed selected support, and the full partite support
embedding. The later EHN projection, strict B-tree stage witnesses,
full native attachment closed test, and schema contradiction must be
proved separately. Do not cite this module as proving the full
stage-level refutation before those certificates are supplied.
-/

namespace StructuralRamsey.Structure.MaximalHardRootFiveCycle

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

/-- One undirected binary relation and NO function symbols. -/
def language : Language where
  RelSymbol := Unit
  FuncSymbol := Empty
  relArity _ := 2
  funcArity := Empty.elim

/-- Complete graph K5, used as the control for PART labels. -/
def control : Structure language (Fin 5) where
  rel R x := by
    cases R
    change (Fin 2 → Fin 5) at x
    exact x 0 ≠ x 1
  func F := Empty.elim F

/-- The irreducible base K2. -/
def base : Structure language (Fin 2) where
  rel R x := by
    cases R
    change (Fin 2 → Fin 2) at x
    exact x 0 ≠ x 1
  func F := Empty.elim F

/-- Old vertex indices: 0=a0, 1=b4, 2=b2, 3=a3, 4=u0, 5=u3.
The first four vertices form the path a0-b4-b2-a3; 4--5 is
the separate A-support edge. -/
def oldPart (x : Fin 6) : Fin 5 :=
  if x = 0 then 0 else
  if x = 1 then 4 else
  if x = 2 then 2 else
  if x = 3 then 3 else
  if x = 4 then 0 else 3

def oldEdge (x y : Fin 6) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
  (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
  (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
  (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4)

def old : Structure language (Fin 6) where
  rel R x := by
    cases R
    change (Fin 2 → Fin 6) at x
    exact oldEdge (x 0) (x 1)
  func F := Empty.elim F

/-- Core vertex indices: 0=c0, 1=d1, 2=c3, 3=w0, 4=w3.
The first three form c0-d1-c3, and 3--4 is the separate
A-support edge. -/
def corePart (x : Fin 5) : Fin 5 :=
  if x = 0 then 0 else
  if x = 1 then 1 else
  if x = 2 then 3 else
  if x = 3 then 0 else 3

def coreEdge (x y : Fin 5) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
  (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
  (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3)

def core : Structure language (Fin 5) where
  rel R x := by
    cases R
    change (Fin 2 → Fin 5) at x
    exact coreEdge (x 0) (x 1)
  func F := Empty.elim F

theorem oldEdge_distinct_parts :
    ∀ x y : Fin 6, oldEdge x y → oldPart x ≠ oldPart y := by
  intro x y h
  fin_cases x <;> fin_cases y <;>
    simp_all [oldEdge, oldPart]

theorem coreEdge_distinct_parts :
    ∀ x y : Fin 5, coreEdge x y → corePart x ≠ corePart y := by
  intro x y h
  fin_cases x <;> fin_cases y <;>
    simp_all [coreEdge, corePart]

/-- The OLD forest is a genuine functional partite system (with
no function symbols). No stage-level EHN assertion is made here. -/
def oldSystem : System language (Fin 5) (Fin 6) where
  toStructure := old
  part := oldPart
  relTransversal := by
    intro R x hEdge i j hpart
    cases R
    change Fin 2 → Fin 6 at x
    change Fin 2 at i
    change Fin 2 at j
    change oldEdge (x 0) (x 1) at hEdge
    have hOld : oldEdge (x 0) (x 1) := hEdge
    have hd : oldPart (x 0) ≠ oldPart (x 1) :=
      oldEdge_distinct_parts (x 0) (x 1) hOld
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hd hpart).elim
    · exact (hd hpart.symm).elim
    · rfl
  funcTransversal := by
    intro F
    exact Empty.elim F

/-- The CORE forest is another genuine functional partite system. -/
def coreSystem : System language (Fin 5) (Fin 5) where
  toStructure := core
  part := corePart
  relTransversal := by
    intro R x hEdge i j hpart
    cases R
    change Fin 2 → Fin 5 at x
    change Fin 2 at i
    change Fin 2 at j
    change coreEdge (x 0) (x 1) at hEdge
    have hCore : coreEdge (x 0) (x 1) := hEdge
    have hd : corePart (x 0) ≠ corePart (x 1) :=
      coreEdge_distinct_parts (x 0) (x 1) hCore
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hd hpart).elim
    · exact (hd hpart.symm).elim
    · rfl
  funcTransversal := by
    intro F
    exact Empty.elim F

/-- Selected old support on parts 0,3. -/
def support : Set (Fin 6) :=
  {x | x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5}

theorem support_closed : old.IsClosed support := by
  intro F
  exact Empty.elim F

/-- Map both copies of the selected A-support to their respective
full substructures in the core: a0↦c0, a3↦c3 and u0↦w0, u3↦w3. -/
def supportMap (x : Fin 6) : Fin 5 :=
  if x = 0 then 0 else
  if x = 3 then 2 else
  if x = 4 then 3 else
  if x = 5 then 4 else 0

/-- Full functional embedding of the actual selected old support
into the core. Unlike a merely positive graph homomorphism, it
reflects the presence and ABSENCE of every relation tuple. -/
def supportEmbedding :
    Embedding (old.induce support support_closed) core where
  toFun := fun x => supportMap x.1
  injective := by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    change a = 0 ∨ a = 3 ∨ a = 4 ∨ a = 5 at ha
    change b = 0 ∨ b = 3 ∨ b = 4 ∨ b = 5 at hb
    rcases ha with (rfl | rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl | rfl) <;>
      simp_all [supportMap]
  map_rel_iff := by
    intro R xs
    cases R
    change Fin 2 → support at xs
    let a : support := xs (0 : Fin 2)
    let b : support := xs (1 : Fin 2)
    change coreEdge (supportMap a.1) (supportMap b.1) ↔
      oldEdge a.1 b.1
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    change a = 0 ∨ a = 3 ∨ a = 4 ∨ a = 5 at ha
    change b = 0 ∨ b = 3 ∨ b = 4 ∨ b = 5 at hb
    rcases ha with (rfl | rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl | rfl) <;>
      simp_all [supportMap, oldEdge, coreEdge]
  map_func := by
    intro F
    exact Empty.elim F

/-- Part preservation on the entire selected support. -/
theorem supportMap_part :
    ∀ x : support, corePart (supportMap x.1) = oldPart x.1 := by
  intro x
  rcases x with ⟨x,hx⟩
  change x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5 at hx
  rcases hx with (rfl | rfl | rfl | rfl) <;>
    simp_all [supportMap, corePart, oldPart]

/-- Native functional PARTITE embedding for the selected support. -/
def supportPartiteEmbedding :
    FunctionalPartite.Embedding
      (oldSystem.induce support support_closed) coreSystem where
  toEmbedding := supportEmbedding
  map_part := supportMap_part

end StructuralRamsey.Structure.MaximalHardRootFiveCycle
