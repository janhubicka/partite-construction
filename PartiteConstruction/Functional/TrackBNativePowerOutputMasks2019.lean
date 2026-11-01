import PartiteConstruction.Functional.Induced

/-!
# Track B: exact output-part active masks in genuine functional powers

The native Hales--Jewett coordinate power uses SAME-OUTPUT-PART
dependent products of genuine set-valued function fibres.

For any output part p, its active mask at an input tuple in the power
is the coordinatewise conjunction of the active mask for p.

Unqualified nonempty-domain masks do NOT obey this conjunction rule
without a common-output-part witness: different coordinates may have
nonempty fibres in incompatible output parts. This source-level
observation does not assert that full OLD canonical tag expansion
commutes with taking an unrelated relational coordinate power.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- A specified output PART occurs at a genuine native power input
if and only if it occurs in EVERY source coordinate. This equality
of active output-part masks is exact on the original power carrier,
for multivalued transversal outputs and all primitive function arities.
No projection homomorphism or nonemptiness of the coordinate set is
required. -/
theorem power_active_outputPart_iff_coordinates
    (B : System L P V) (N : ℕ)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Vertex B N) (p : P) :
    (∃ y : Vertex B N,
      y ∈ (power B N).func F xs ∧ y.part = p) ↔
      ∀ i : Fin N,
        ∃ z : V,
          z ∈ B.func F (fun j => (xs j).coord i) ∧
          B.part z = p := by
  classical
  constructor
  · rintro ⟨y, hy, hp⟩ i
    exact ⟨y.coord i, hy i, (y.belongs i).trans hp⟩
  · intro h
    choose coord hMem hPart using h
    let y : Vertex B N :=
      { part := p
        coord := coord
        belongs := hPart }
    exact ⟨y, hMem, rfl⟩

/-- The exact unqualified active-domain rule for a genuine functional
power uses ONE COMMON output part across all coordinates.

It is NOT merely the conjunction of unqualified nonempty input-domain
bits. That invalid distributivity would drop the output-part alignment
required by genuine partite systems. -/
theorem power_nonempty_iff_common_outputPart
    (B : System L P V) (N : ℕ)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Vertex B N) :
    ((power B N).func F xs).Nonempty ↔
      ∃ p : P, ∀ i : Fin N,
        ∃ z : V,
          z ∈ B.func F (fun j => (xs j).coord i) ∧
          B.part z = p := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.part,
      (power_active_outputPart_iff_coordinates B N F xs y.part).mp
        ⟨y, hy, rfl⟩⟩
  · rintro ⟨p, hp⟩
    obtain ⟨y, hy, _⟩ :=
      (power_active_outputPart_iff_coordinates B N F xs p).mpr hp
    exact ⟨y, hy⟩

end StructuralRamsey.FunctionalPartite.Induced
