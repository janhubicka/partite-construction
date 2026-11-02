import PartiteConstruction.Functional.TrackBPowerFreshFullRoot2019

/-!
# Track B: a fresh FULL U-root tag can survive a coordinate root collapse

When an actual native Hales--Jewett power has globally distinct input
root WORDS, it may still identify two root coordinates at one source
coordinate. If one common output PART is supported by every source
coordinate, the true native power admits a genuine full function value
over that global root.

The complete canonical OLD root of that real output defines a valid
fresh 2019 U-closure tag on the ACTUAL native power vertices. Yet the
SAME equality-pattern domain symbol fails in a collapsed source
coordinate, since its input root there is not injective.

Thus neither OLD domain relations nor their fresh U-tags can be
unconditionally computed by taking a plain coordinatewise product of
OLD-tagged source structures. The theorem is conditional on a real
power input/output configuration, not an invented final Ramsey witness.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- A genuine native-power global root with common-part output has a
CANONICAL complete fresh U-tag, even if a coordinate fails the old
equality-pattern domain test because its root vertices collide.

No replacement of actual power vertices, nonclosed weak source hull,
or illicit full projection is involved. Positive pattern root size is
the genuine 2019 fresh closure description requirement. -/
theorem nativePower_canonicalFreshTag_coordinateCollapse
    (B : System L P V) (N : ℕ)
    (pat : Language.FunctionInputPattern L)
    (hPositive : 0 < pat.rootSize)
    (roots : Fin pat.rootSize → Vertex B N)
    (i : Fin N)
    (hInjective : Function.Injective roots)
    (hCommon : ∃ q : P, ∀ j : Fin N,
      ∃ z : V,
        z ∈ B.func pat.symbol
          (fun k => (roots (pat.argMap k)).coord j) ∧ B.part z = q)
    (hCollapse : ¬ Function.Injective
      (fun k : Fin pat.rootSize => (roots k).coord i)) :
    ∃ (out : Vertex B N) (fresh : Language.FunctionRootPattern L),
      fresh.input = pat ∧
      (patternTagExpansion ((power B N).toStructure.patternGraph)).rel
        (.inr fresh) (Structure.funcTuple roots out) ∧
      ¬ (B.toStructure.patternGraph).rel (.inr (.inl pat))
          (fun k : Fin pat.rootSize => (roots k).coord i) := by
  classical
  obtain ⟨q, hq⟩ := hCommon
  choose coord hVal hPart using hq
  let out : Vertex B N := {
    part := q
    coord := coord
    belongs := hPart
  }
  have hValue :
      out ∈ (power B N).func pat.symbol (roots ∘ pat.argMap) :=
    hVal
  have hOld :
      ((power B N).toStructure.patternGraph).rel (.inr (.inr pat))
        (Structure.funcTuple roots out) := by
    change
      Function.Injective
        (fun j : Fin pat.rootSize =>
          (Structure.funcTuple roots out) j.castSucc) ∧
      (Structure.funcTuple roots out) (Fin.last pat.rootSize) ∈
        (power B N).func pat.symbol
          ((fun j : Fin pat.rootSize =>
            (Structure.funcTuple roots out) j.castSucc) ∘ pat.argMap)
    simpa only [Structure.funcTuple_castSucc, Structure.funcTuple_last]
      using (show Function.Injective roots ∧
          out ∈ (power B N).func pat.symbol (roots ∘ pat.argMap)
        from ⟨hInjective, hValue⟩)
  obtain ⟨fresh, hInput, hTag⟩ :=
    nativePower_oldOutput_admits_canonicalFreshRoot
      B N pat hPositive (Structure.funcTuple roots out) hOld
  have hFail :
      ¬ (B.toStructure.patternGraph).rel (.inr (.inl pat))
          (fun k : Fin pat.rootSize => (roots k).coord i) := by
    intro hCoord
    exact hCollapse hCoord.1
  exact ⟨out, fresh, hInput, hTag, hFail⟩

end StructuralRamsey.FunctionalPartite.Induced
