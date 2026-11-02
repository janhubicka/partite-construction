import PartiteConstruction.Functional.TrackBPowerFreshRootCollision2019

/-!
# Track B: actual finite 3-vertex failure of naive OLD-tagged power

Use three original vertices 0,1,2 with part(0)=part(1)=0,
part(2)=1. A single BINARY set-valued function has the ONE
defined output {2} on every input pair. There are no primitive
relations. This is an honest transversal functional partite system:
all its function values lie in the one output part, and each
per-part function value is unique.

In its TRUE two-coordinate native Hales--Jewett power, the two
input words (0,0) and (0,1) are distinct global power vertices,
but coincide at coordinate zero. The binary function produces
(2,2), so the actual power has a genuine OLD output relation
and its canonical full-root fresh 2019 U-closure tag.

The coordinate-zero OLD domain with the SAME distinct-input
equality pattern is FALSE because the two source inputs there
are equal. Thus the naive coordinatewise OLD (and hence tagged)
relational power is not the native tagged functional power.

This is a finite genuine example with no abstract common-output
hypothesis and no surrogate Ramsey or strict B-tree target.
-/

namespace StructuralRamsey.FunctionalPartite.Induced.TrackBFinite

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

/-- One genuine binary function symbol and no primitive relations. -/
def lang : Language where
  RelSymbol := PEmpty
  FuncSymbol := PUnit
  relArity := fun R => PEmpty.elim R
  funcArity := fun _ => 2

/-- Three original vertices, with two distinct inputs in part zero. -/
def part (x : Fin 3) : Fin 2 :=
  if x.val < 2 then 0 else 1

/-- Every defined binary application has the unique output vertex 2.
This is a transversal native System, not an invented tagged relation. -/
def source : System lang (Fin 2) (Fin 3) where
  toStructure := {
    rel := fun R _ => PEmpty.elim R
    func := fun _ _ => { (2 : Fin 3) }
  }
  part := part
  relTransversal := by
    intro R xs hRel i j hParts
    exact PEmpty.elim R
  funcTransversal := by
    intro F xs y z hy hz hPart
    change y = (2 : Fin 3) at hy
    change z = (2 : Fin 3) at hz
    exact hy.trans hz.symm

/-- The binary input symbol uses both actual distinct inputs. -/
def binaryPattern : Language.FunctionInputPattern lang where
  symbol := PUnit.unit
  rootSize := 2
  argMap := fun i => i
  onto := by intro i; exact ⟨i, rfl⟩

/-- The ACTUAL function-language two-coordinate power has a valid
canonical fresh full-root tag over two globally distinct input words,
although the SAME OLD input-pattern domain relation is false at
coordinate zero.

Thus a coordinatewise relation-product interpretation of these
OLD and fresh tagged symbols is genuinely false on a concrete
finite transversal partial-function structure. -/
theorem actualNativePower_freshRoot_not_coordinatewiseOld :
    ∃ roots : Fin 2 → Vertex source 2,
      ∃ (out : Vertex source 2)
        (fresh : Language.FunctionRootPattern lang),
        fresh.input = binaryPattern ∧
        (patternTagExpansion ((power source 2).toStructure.patternGraph)).rel
          (.inr fresh) (Structure.funcTuple roots out) ∧
        ¬ (source.toStructure.patternGraph).rel
          (.inr (.inl binaryPattern))
            (fun j : Fin binaryPattern.rootSize =>
              (roots j).coord (0 : Fin 2)) := by
  have hDistinct : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hSamePart : source.part (0 : Fin 3) =
      source.part (1 : Fin 3) := by decide
  obtain ⟨roots, hInjective, hCollide⟩ :=
    nativePower_globalInjective_coordinateCollision
      source (0 : Fin 3) (1 : Fin 3) hDistinct hSamePart
  have hCommon : ∃ q : Fin 2, ∀ j : Fin 2,
      ∃ z : Fin 3,
        z ∈ source.func binaryPattern.symbol
          (fun k => (roots (binaryPattern.argMap k)).coord j) ∧
        source.part z = q := by
    refine ⟨1, ?_⟩
    intro j
    refine ⟨2, ?_, ?_⟩
    · change (2 : Fin 3) ∈ ({(2 : Fin 3)} : Set (Fin 3))
      simp
    · decide
  refine ⟨roots, ?_⟩
  exact nativePower_canonicalFreshTag_coordinateCollapse
    source 2 binaryPattern (by decide) roots (0 : Fin 2)
      hInjective hCommon hCollide

end StructuralRamsey.FunctionalPartite.Induced.TrackBFinite
