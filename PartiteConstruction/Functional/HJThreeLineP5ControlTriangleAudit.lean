import PartiteConstruction.Functional.HJThreeLineNativeOldP5
import PartiteConstruction.Functional.WeakInvariant

/-!
# Track D adversarial gate: the native old P5 forces a triangular control

The actual five-vertex old path a1--a0--c--b1--b0 has three
part labels 0,1,2. Its edges 0--1, 0--4, and 3--4 project
to ALL THREE edges of a triangle in the part control.

Consequently any part control D receiving even the globally WEAK
EHN relation/function projection of this old P5 must contain that
triangle and is NOT bipartite. This formalizes why the beautiful
three-line C7 native counterexample is not a counterexample to the
rank-successor theorem's actual strict-K2 predecessor hypothesis:
the necessary control is already unsuitable for K2-tree locality
at rank >=3. Showing failure of a specific tree-completion
predicate would additionally use the separate K2-tree
bipartiteness bridge; it is not claimed here.

No Ramsey arrow for unordered K2 embeddings into K3 is assumed.
The theorem uses exactly the full-functional native source and the
2019/EHN WEAK forward relation condition, with no artificial
source-undefined function-reflection premise.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

/-- The three oriented graph edges of a triangular part control. -/
def HasTriangle (D : Structure Lang (Fin 3)) : Prop :=
  D.rel () (fun k : Fin 2 => if k = 0 then 0 else 1) ∧
  D.rel () (fun k : Fin 2 => if k = 0 then 0 else 2) ∧
  D.rel () (fun k : Fin 2 => if k = 0 then 1 else 2)

/-- Any forward graph homomorphism from the original native
P5 along its actual three-part projection forces every edge
of a triangle in the control. -/
theorem weak_oldPart_forces_triangle
    (D : Structure Lang (Fin 3))
    (h : oldSystem.toStructure.IsWeakHomomorphism D oldPart) :
    HasTriangle D := by
  have edgeMap (a b : Fin 5) (p q : Fin 3)
      (hEdge : oldEdge a b)
      (hpa : oldPart a = p) (hpb : oldPart b = q) :
      D.rel () (fun k : Fin 2 => if k = 0 then p else q) := by
    let args : Fin 2 → Fin 5 := fun k => if k = 0 then a else b
    have hOld : oldSystem.toStructure.rel () args := by
      change oldEdge a b
      exact hEdge
    have hD := h.1 () args hOld
    have hArgs : oldPart ∘ args =
        (fun k : Fin 2 => if k = 0 then p else q) := by
      funext k
      fin_cases k
      · exact hpa
      · exact hpb
    rw [hArgs] at hD
    exact hD
  refine ⟨?_, ?_, ?_⟩
  · exact edgeMap 0 1 0 1
      (by simp [oldEdge]) (by decide) (by decide)
  · exact edgeMap 0 4 0 2
      (by simp [oldEdge]) (by decide) (by decide)
  · exact edgeMap 3 4 1 2
      (by simp [oldEdge]) (by decide) (by decide)

/-- A triangle cannot have a proper two-colouring, in ANY
graph signature (including a graph-only functional Structure).
The three edges are literal relation tuples, not hypothetical
weakly reflected nonedges. -/
theorem triangle_not_twoColorable
    (D : Structure Lang (Fin 3))
    (hTri : HasTriangle D) :
    ¬ ∃ c : Fin 3 → Bool,
      ∀ x y : Fin 3,
        D.rel () (fun k : Fin 2 => if k = 0 then x else y) →
        c x ≠ c y := by
  rintro ⟨c, hc⟩
  have h01 : c 0 ≠ c 1 := hc 0 1 hTri.1
  have h02 : c 0 ≠ c 2 := hc 0 2 hTri.2.1
  have h12 : c 1 ≠ c 2 := hc 1 2 hTri.2.2
  cases h0 : c 0 <;> cases h1 : c 1 <;>
    cases h2 : c 2 <;> simp_all

/-- The actual P5 part projection cannot be an EHN
weak homomorphism to any bipartite three-part control. -/
theorem oldPart_no_bipartite_weak_control
    (D : Structure Lang (Fin 3))
    (h : oldSystem.toStructure.IsWeakHomomorphism D oldPart) :
    ¬ ∃ c : Fin 3 → Bool,
      ∀ x y : Fin 3,
        D.rel () (fun k : Fin 2 => if k = 0 then x else y) →
        c x ≠ c y :=
  triangle_not_twoColorable D
    (weak_oldPart_forces_triangle D h)

/-- Even the full EHN partite-over-control invariant of the
old source forces a triangle in the control. This identifies
the precise predecessor-locality blocker in the native C7
regression; it does not assert an unrealized Ramsey arrow. -/
theorem oldPart_weaklyPartite_forces_triangle
    (D : Structure Lang (Fin 3))
    (h : oldSystem.WeaklyPartiteOver D) :
    HasTriangle D :=
  weak_oldPart_forces_triangle D h.1

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7
