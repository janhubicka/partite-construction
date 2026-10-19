import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge
import PartiteConstruction.Functional.Induced

/-!
# The canonical output-part singleton split respects the TRUE native HJ power

Every genuine multivalued functional partite system B is represented
without loss by the canonical singleton function language (F,q).
The original full partite projection to functional control A remains
a FULL partite projection to the singleton split of the transversal
control A, because the original projected WHOLE function fibres
contain every required output part.

For a POSITIVE Hales--Jewett power length N, splitting the actual
coordinatewise native functional power has exactly the same
per-coordinate (F,q) output membership predicate as taking the
coordinatewise power of the canonical singleton split. No relational
surrogate Picture, singleton assumption on the original fibres, or
generated closure of the vertex set is used.

N>0 is essential: at N=0 coordinatewise output conditions are
vacuous, while singletonization still constrains the output part.
This is the static HJ core/power bridge, not a theorem about
incompatible arbitrary finite line-attachment TARGET histories.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- Splitting native multivalued output fibres into one partial
singleton function (F,q) for each output part q preserves the
full PARTITE PROJECTION to the analogously split control.

In particular, this is whole-fibre surjectivity for EVERY
(F,q), not merely the positive-image half of an EHN map. -/
theorem System.splitOutputParts_projectionHom
    (B : System L P V) (A : Structure L P)
    (hB : B.ProjectionHom A) :
    (B.splitOutputParts).ProjectionHom
      ((transversal A).splitOutputParts).toStructure := by
  constructor
  · intro R xs hx
    exact hB.1 R.down xs hx
  · intro Fq xs
    rcases Fq with ⟨F, q⟩
    change imageSet B.part
        {y : V | y ∈ B.func F.down xs ∧ B.part y = q} =
      {p : P | p ∈ A.func F.down (B.part ∘ xs) ∧ p = q}
    ext p
    constructor
    · rintro ⟨y, ⟨hy, hyq⟩, rfl⟩
      refine ⟨?_, hyq⟩
      have him : B.part y ∈ imageSet B.part (B.func F.down xs) :=
        ⟨y, hy, rfl⟩
      rw [hB.2 F.down xs] at him
      exact him
    · rintro ⟨hp, hq⟩
      have him : p ∈ imageSet B.part (B.func F.down xs) := by
        rw [hB.2 F.down xs]
        exact hp
      obtain ⟨y, hy, hyp⟩ := him
      exact ⟨y, ⟨hy, hyp.trans hq⟩, hyp⟩

namespace Induced

/-- EXACT positive-length native Hales--Jewett per-output-part
function membership law. A native power vertex has all
coordinates in the SAME original output part. Hence the
singleton split of the true power has (F,q) output precisely
when EVERY coordinate has the corresponding original F-value
IN THE SAME q-output fibre.

No extra vertices, chosen function order, or generated closure.
The N>0 hypothesis cannot be removed (empty-product counterexample). -/
theorem power_splitOutputParts_func_iff
    (B : System L P V)
    (N : ℕ) (hN : 0 < N)
    (F : L.FuncSymbol) (q : P)
    (xs : Fin (L.funcArity F) → Vertex B N)
    (y : Vertex B N) :
    y ∈ ((power B N).splitOutputParts).func
        ((ULift.up F : ULift.{max u v, u} L.FuncSymbol),q) xs ↔
      ∀ i : Fin N,
        y.coord i ∈ B.func F (fun j => (xs j).coord i) ∧
          B.part (y.coord i) = q := by
  change
    ((∀ i : Fin N,
        y.coord i ∈ B.func F (fun j => (xs j).coord i)) ∧
      y.part = q) ↔ _
  constructor
  · rintro ⟨hFunction, hPart⟩ i
    exact ⟨hFunction i, (y.belongs i).trans hPart⟩
  · intro h
    refine ⟨(fun i => (h i).1), ?_⟩
    let i : Fin N := ⟨0, hN⟩
    exact (y.belongs i).symm.trans (h i).2

end Induced
end StructuralRamsey.FunctionalPartite
