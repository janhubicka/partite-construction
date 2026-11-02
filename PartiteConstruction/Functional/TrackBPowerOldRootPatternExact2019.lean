import PartiteConstruction.Functional.TrackBNativePowerTaggedLineTransport2019
import PartiteConstruction.Functional.PartialFunctionPatternGraph2019

/-!
# Track B: exact OLD equality-pattern relations of genuine native HJ powers

The 2019 OLD relational language has one active-domain relation and
one output relation for each surjective input equality pattern.
For the TRUE native function-language Hales--Jewett coordinate power:

* injectivity of a displayed distinct-input root is checked on the
  WHOLE power vertices, not coordinatewise;
* a domain is active exactly when a SINGLE output part occurs at
  every coordinate; this is stronger than independent coordinate
  nonemptiness unless a common control projection is available;
* an OLD output tuple is realized precisely when the global root
  is injective and its output word is a genuine coordinatewise
  function value.

Thus canonical OLD tagging must be performed AFTER forming the
native power, using its genuine global equality patterns. It is
not equivalent to naïvely requiring each coordinate's OLD
root to realize the same injective input pattern.

Every theorem is on literal native power vertices and changes
neither the underlying power nor any weak test carrier.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- Actual OLD active-domain masks of a genuine functional power:
global injectivity of the FULL distinct-input root, together with a
common output part that is realized in every source coordinate.

The primitive arguments may repeat according to pat.argMap. No
injectivity of a coordinate projection of the root is assumed. -/
theorem nativePower_oldDomainPattern_iff
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (roots : Fin pat.rootSize → Vertex B N) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inl pat)) roots ↔
      Function.Injective roots ∧
        ∃ q : P, ∀ i : Fin N,
          ∃ z : V,
            z ∈ B.func pat.symbol
              (fun k => (roots (pat.argMap k)).coord i) ∧
            B.part z = q := by
  constructor
  · rintro ⟨hInj, hDomain⟩
    exact ⟨hInj,
      (power_nonempty_iff_common_outputPart B N
        pat.symbol (roots ∘ pat.argMap)).mp hDomain⟩
  · rintro ⟨hInj, hPart⟩
    exact ⟨hInj,
      (power_nonempty_iff_common_outputPart B N
        pat.symbol (roots ∘ pat.argMap)).mpr hPart⟩

/-- All OLD output-graph tuples of the ACTUAL native power:
the entire displayed input root is injective and the selected
OUTPUT WORD belongs to the native power function fibre exactly
when all its coordinates belong to the corresponding source fibres.

Unlike a naïve product of OLD equality-pattern relational graphs,
the root is NOT required to be injective in each individual
coordinate, only as a function into the actual power vertex type. -/
theorem nativePower_oldOutputPattern_iff
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (tuple : Fin (pat.rootSize + 1) → Vertex B N) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inr pat)) tuple ↔
      Function.Injective (fun j : Fin pat.rootSize =>
        tuple (Fin.castSucc j)) ∧
      ∀ i : Fin N,
        (tuple (Fin.last pat.rootSize)).coord i ∈
          B.func pat.symbol
            (fun k => (tuple (Fin.castSucc (pat.argMap k))).coord i) := by
  rfl

/-- Under a genuine native projection B -> A and positive power
length, the OLD domain relation is determined by the ORIGINAL
control's function domain together with global root injectivity.
No false coordinatewise OLD pattern condition is introduced. -/
theorem nativePower_oldDomainPattern_control_iff
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    (N : ℕ) (hN : 0 < N)
    (pat : Language.FunctionInputPattern L)
    (roots : Fin pat.rootSize → Vertex B N) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inl pat)) roots ↔
      Function.Injective roots ∧
        (A.func pat.symbol
          (fun k => (roots (pat.argMap k)).part)).Nonempty := by
  constructor
  · rintro ⟨hInj, hDom⟩
    exact ⟨hInj, (power_nonempty_iff_control A B hB N hN
      pat.symbol (roots ∘ pat.argMap)).mp hDom⟩
  · rintro ⟨hInj, hDom⟩
    exact ⟨hInj, (power_nonempty_iff_control A B hB N hN
      pat.symbol (roots ∘ pat.argMap)).mpr hDom⟩

/-- A genuine OLD domain pattern of the native power may fail as the
SAME OLD domain pattern in a coordinate: the global power root can
be injective even when some coordinate root collapses.

The hypothesis hCommon certifies a REAL source-defined power
function domain. This is an explicit obstruction to a naïve
coordinatewise OLD-pattern-product equivalence, not to the actual
2019 tagged construction on the native power. -/
theorem nativePower_oldDomainPattern_coordinateCollapse
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (roots : Fin pat.rootSize → Vertex B N)
    (i : Fin N)
    (hInj : Function.Injective roots)
    (hCommon : ∃ q : P, ∀ j : Fin N,
      ∃ z : V,
        z ∈ B.func pat.symbol
          (fun k => (roots (pat.argMap k)).coord j) ∧ B.part z = q)
    (hCollide : ¬ Function.Injective
      (fun k : Fin pat.rootSize => (roots k).coord i)) :
    ((power B N).toStructure.patternGraph).rel (.inr (.inl pat)) roots ∧
      ¬ (B.toStructure.patternGraph).rel (.inr (.inl pat))
        (fun k : Fin pat.rootSize => (roots k).coord i) := by
  refine ⟨(nativePower_oldDomainPattern_iff B N pat roots).mpr
      ⟨hInj, hCommon⟩, ?_⟩
  intro hOld
  exact hCollide hOld.1

/-- Even on a genuine partite power, global equality of power words
and equality at a single coordinate are different notions. Two
distinct original same-part vertices yield a TWO-coordinate
power root injective globally but collapsing at coordinate zero.

This unconditional shape witness has no function-domain hypothesis:
it isolates exactly the equality-pattern issue separately from
the compatibility of output-part masks. -/
theorem nativePower_globalInjective_coordinateCollision
    (B : System L P V) (a b : V)
    (hab : a ≠ b) (hpart : B.part a = B.part b) :
    ∃ roots : Fin 2 → Vertex B 2,
      Function.Injective roots ∧
        ¬ Function.Injective
          (fun j : Fin 2 => (roots j).coord (0 : Fin 2)) := by
  let x : Vertex B 2 := {
    part := B.part a
    coord := fun _ => a
    belongs := by intro _; rfl
  }
  let y : Vertex B 2 := {
    part := B.part a
    coord := fun i => if i = (0 : Fin 2) then a else b
    belongs := by
      intro i
      by_cases hi : i = (0 : Fin 2)
      · simp [hi]
      · simp [hi, hpart]
  }
  have hxy : x ≠ y := by
    intro heq
    have h := congrArg
      (fun t : Vertex B 2 => t.coord (1 : Fin 2)) heq
    exact hab (by simpa [x, y] using h)
  let roots : Fin 2 → Vertex B 2 :=
    fun j => if j = (0 : Fin 2) then x else y
  refine ⟨roots, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hxy (by simpa [roots] using hij)).elim
    · exact (hxy (by simpa [roots] using hij.symm)).elim
    · rfl
  · intro hI
    have hCoord :
        (roots (0 : Fin 2)).coord (0 : Fin 2) =
          (roots (1 : Fin 2)).coord (0 : Fin 2) := by
      simp [roots, x, y]
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
      (hI hCoord)

end StructuralRamsey.FunctionalPartite.Induced
