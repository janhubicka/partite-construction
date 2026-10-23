import PartiteConstruction.Functional.MaximalHardRootFiveCycleFixture
import PartiteConstruction.Structure.FreeAmalgamationClass
import PartiteConstruction.Functional.WeakInvariant

/-!
# The arbitrary-stage native C5 fixture belongs to an actual free class

The native hard-root counterexample is in the function-free undirected
graph language, with complete-graph control K5. Every old/core forest
relation tuple projects to an edge of this control, because its two
endpoints occupy distinct control parts.

The universal class of all structures in this language is hereditary
and closed under FULL free amalgamation. Thus class membership is
not the obstruction. The next, more subtle step is the EHN local
irreducible-embedding property of the OLD and CORE part maps and their
strict K2-tree predecessor-rank completions.

This file certifies only these deliberately elementary class and
global positive map obligations. No total-fibre projection, closure
inflation or HJ-power assertion is introduced.
-/

namespace StructuralRamsey.Structure.MaximalHardRootFiveCycle

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

/-- The universal class in the function-free native graph language. -/
def allStructuresClass : StructureClass (L := language) :=
  fun _ => True

/-- Free amalgamation and hereditariness of the universal class are
automatic, for the ACTUAL full function-language class interface. -/
theorem allStructuresClass_free :
    FreeAmalgamationClass allStructuresClass := by
  constructor <;> intros <;> trivial

theorem old_mem_allStructuresClass : allStructuresClass old := trivial
theorem core_mem_allStructuresClass : allStructuresClass core := trivial
theorem base_mem_allStructuresClass : allStructuresClass base := trivial
theorem control_mem_allStructuresClass : allStructuresClass control := trivial

/-- The OLD forest has a genuine full-value global projection into
the complete graph K5, because each relation joins distinct parts
and there are no functions. This does not yet assert EHN reflection
on all full irreducible substructures. -/
theorem old_projectionHom :
    oldSystem.ProjectionHom control := by
  constructor
  · intro R t hRel
    cases R
    change oldEdge (t 0) (t 1) at hRel
    change oldPart (t 0) ≠ oldPart (t 1)
    exact oldEdge_distinct_parts (t 0) (t 1) hRel
  · intro F
    exact Empty.elim F

/-- Same global relation projection for the CORE forest. -/
theorem core_projectionHom :
    coreSystem.ProjectionHom control := by
  constructor
  · intro R t hRel
    cases R
    change coreEdge (t 0) (t 1) at hRel
    change corePart (t 0) ≠ corePart (t 1)
    exact coreEdge_distinct_parts (t 0) (t 1) hRel
  · intro F
    exact Empty.elim F

/-- For the unrestricted original-2019 partial-map stage interface,
both global projections are at least WEAK; the remaining EHN condition
is a separate LOCAL reflection requirement. -/
theorem old_projectionWeak :
    old.IsWeakHomomorphism control oldPart := by
  constructor
  · exact old_projectionHom.1
  · intro F
    exact Empty.elim F

theorem core_projectionWeak :
    core.IsWeakHomomorphism control corePart := by
  constructor
  · exact core_projectionHom.1
  · intro F
    exact Empty.elim F

end StructuralRamsey.Structure.MaximalHardRootFiveCycle
