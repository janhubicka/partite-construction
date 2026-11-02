import PartiteConstruction.Functional.TrackBPowerOldRootPatternExact2019

/-!
# Track B: exact repair of OLD coordinatewise root tests

On part-INJECTIVE distinct-input roots of a genuine native power,
global power-root injectivity does imply injectivity in EVERY
coordinate: equality of two coordinate vertices forces equality of
their part labels and hence equality of the root indices.

This is the correct condition under which a coordinatewise 2019
OLD domain check can be compared with the native one. The stronger
equivalence with UNQUALIFIED coordinate domain bits requires
a true native full projection to a COMMON control and positive
power length, ensuring every source coordinate sees the same
output-part set.

Neither assertion claims that the complete canonical fresh
root-tagged structure commutes with coordinatewise OLD power.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- DISTINCT PARTS of the displayed native power root force
injectivity of its vertex coordinates at EVERY coordinate i.
The conclusion is stronger than the generic global injectivity
condition, which by itself admits coordinate collisions. -/
theorem nativePower_coordinateRoot_injective_of_partInjective
    (B : System L P V) (N m : ℕ)
    (roots : Fin m → Vertex B N)
    (hParts : Function.Injective (fun j => (roots j).part))
    (i : Fin N) :
    Function.Injective (fun j : Fin m => (roots j).coord i) := by
  intro j k h
  apply hParts
  calc
    (roots j).part = B.part ((roots j).coord i) :=
      ((roots j).belongs i).symm
    _ = B.part ((roots k).coord i) := congrArg B.part h
    _ = (roots k).part := (roots k).belongs i

/-- With part-injective distinct input roots, the ACTUAL native OLD
domain root equals the SAME coordinatewise OLD domain patterns
PLUS ONE common output part realized at every coordinate.

This is an exact qualified comparison; the common-part condition
cannot be dropped merely from source-coordinate nonemptiness when
the source has no true common part projection. -/
theorem nativePower_oldDomainPattern_transversal_iff
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (roots : Fin pat.rootSize → Vertex B N)
    (hParts : Function.Injective (fun j => (roots j).part)) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inl pat)) roots ↔
      ∃ q : P, ∀ i : Fin N,
        ((B.toStructure.patternGraph).rel (.inr (.inl pat))
          (fun j : Fin pat.rootSize => (roots j).coord i)) ∧
        ∃ z : V,
          z ∈ B.func pat.symbol
            (fun k => (roots (pat.argMap k)).coord i) ∧
          B.part z = q := by
  constructor
  · intro hNative
    obtain ⟨_, q, hq⟩ :=
      (nativePower_oldDomainPattern_iff B N pat roots).mp hNative
    refine ⟨q, ?_⟩
    intro i
    obtain ⟨z, hz, hPart⟩ := hq i
    refine ⟨?_, ⟨z, hz, hPart⟩⟩
    exact ⟨nativePower_coordinateRoot_injective_of_partInjective
      B N pat.rootSize roots hParts i, ⟨z, hz⟩⟩
  · rintro ⟨q, hq⟩
    apply (nativePower_oldDomainPattern_iff B N pat roots).mpr
    refine ⟨?_, ⟨q, fun i => (hq i).2⟩⟩
    intro j k hEq
    exact hParts (congrArg
      (fun x : Vertex B N => x.part) hEq)

/-- The true common control identifies all source coordinate
output-part sets. For a POSITIVE native power and part-injective
root, the original OLD-domain predicate holds if and only if
it holds separately at EVERY source coordinate.

Without part injectivity, the coordinatewise implications are
false because global power root equality patterns can collapse
in individual coordinates. Without a full ProjectionHom, source
coordinates can have incompatible output-part sets. -/
theorem nativePower_oldDomainPattern_transversal_control_iff
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    (N : ℕ) (hN : 0 < N)
    (pat : Language.FunctionInputPattern L)
    (roots : Fin pat.rootSize → Vertex B N)
    (hParts : Function.Injective (fun j => (roots j).part)) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inl pat)) roots ↔
      ∀ i : Fin N,
        (B.toStructure.patternGraph).rel (.inr (.inl pat))
          (fun j : Fin pat.rootSize => (roots j).coord i) := by
  constructor
  · intro hNative i
    obtain ⟨_, q, hq⟩ :=
      (nativePower_oldDomainPattern_iff B N pat roots).mp hNative
    obtain ⟨z, hz, _⟩ := hq i
    exact ⟨nativePower_coordinateRoot_injective_of_partInjective
      B N pat.rootSize roots hParts i, ⟨z, hz⟩⟩
  · intro hAll
    have hInj : Function.Injective roots := by
      intro j k hEq
      exact hParts (congrArg (fun x : Vertex B N => x.part) hEq)
    have hOld := (hAll ⟨0, hN⟩).2
    obtain ⟨z, hz⟩ := hOld
    let args : Fin (L.funcArity pat.symbol) → V :=
      fun k => (roots (pat.argMap k)).coord ⟨0, hN⟩
    have hPartArgs :
        B.part ∘ args =
          (fun k : Fin (L.funcArity pat.symbol) =>
            (roots (pat.argMap k)).part) := by
      funext k
      exact (roots (pat.argMap k)).belongs ⟨0, hN⟩
    have hMapped :
        B.part z ∈ Structure.imageSet B.part (B.func pat.symbol args) :=
      ⟨z, hz, rfl⟩
    rw [hB.2 pat.symbol args, hPartArgs] at hMapped
    apply (nativePower_oldDomainPattern_control_iff
      A B hB N hN pat roots).mpr
    exact ⟨hInj, ⟨B.part z, hMapped⟩⟩

end StructuralRamsey.FunctionalPartite.Induced
