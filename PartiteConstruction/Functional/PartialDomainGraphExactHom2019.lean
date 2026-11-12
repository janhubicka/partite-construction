import PartiteConstruction.Structure.PartialSetFunctionsDomainGraph
import PartiteConstruction.Structure.Relationalize

/-!
# Track A: precise source-defined partial homomorphism / relational graph contract

A positive relational homomorphism between the separate domain-and-output
graphs is necessary for a source-defined partial-function homomorphism, but
is not sufficient: it only preserves inclusion of the mapped output set.
The missing condition is that *each target output at an image of a defined
source input* already comes from some source output.

This file gives the exact equivalence for arbitrary function arities,
including nullaries, repeated inputs and genuinely defined-empty values.
Neither injectivity nor domain reflection is assumed. Source-undefined
applications are wholly unconstrained.

This is a source-level map dictionary. It does not assert any
homomorphism-embedding theorem or strict functional B-tree completion.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- No EXTRA target function outputs are allowed over an image of a
DEFINED source application. Equivalently, the output graph map is
surjective on every source-defined function fibre. -/
def NoExtraTargetOutputsOnDefined
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (U : Set V), A.func F xs = some U →
    ∀ y : W, B.HasOutput F (f ∘ xs) y →
      y ∈ Structure.imageSet f U

/-- An exact (not just positive) characterization of original-2019-style
partial function homomorphisms in the two-relation domain/output language.

Crucially, `NoExtraTargetOutputsOnDefined` is imposed only at
source-defined tuples. The target may define new operations at
source-undefined inputs, which must not be ruled out by a spurious
domain-reflection requirement. -/
theorem originalPartialHom_iff_domainGraphHom_and_noExtra
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) :
    IsOriginalPartialHomomorphism A B f ↔
      (domainGraph A).IsHomomorphism (domainGraph B) f ∧
        NoExtraTargetOutputsOnDefined A B f := by
  constructor
  · intro h
    refine ⟨h.to_domainGraph_hom, ?_⟩
    intro F xs U hU y hy
    obtain ⟨T, hT, hyT⟩ := hy
    have hTU : T = Structure.imageSet f U :=
      Option.some.inj (hT.symm.trans (h.2 F xs U hU))
    simpa only [hTU] using hyT
  · rintro ⟨hGraph, hNoExtra⟩
    constructor
    · intro R xs hR
      exact hGraph (.inl R) xs hR
    · intro F xs U hU
      have hDom : B.Defined F (f ∘ xs) :=
        hGraph (.inr (.inl F)) xs (show A.Defined F xs from ⟨U, hU⟩)
      obtain ⟨T, hT⟩ := hDom
      have hSet : T = Structure.imageSet f U := by
        ext y
        constructor
        · intro hy
          exact hNoExtra F xs U hU y ⟨T, hT, hy⟩
        · rintro ⟨z, hz, rfl⟩
          have hOutA :
              (domainGraph A).rel (.inr (.inr F))
                (Structure.funcTuple xs z) := by
            simpa only [domainGraph, Structure.funcTuple_castSucc,
              Structure.funcTuple_last] using
                (show A.HasOutput F xs z from ⟨U, hU, hz⟩)
          have hOutB :
              (domainGraph B).rel (.inr (.inr F))
                (Structure.funcTuple (f ∘ xs) (f z)) := by
            have hStep := hGraph (.inr (.inr F))
              (Structure.funcTuple xs z) hOutA
            have hTuple : f ∘ Structure.funcTuple xs z =
                Structure.funcTuple (f ∘ xs) (f z) :=
              Structure.comp_funcTuple f xs z
            rw [hTuple] at hStep
            exact hStep
          have hTarget : B.HasOutput F (f ∘ xs) (f z) := by
            simpa only [domainGraph, Structure.funcTuple_castSucc,
              Structure.funcTuple_last] using hOutB
          obtain ⟨T', hT', hzT'⟩ := hTarget
          have hTT' : T' = T :=
            Option.some.inj (hT'.symm.trans hT)
          simpa only [hTT'] using hzT'
      rw [hSet] at hT
      exact hT

end StructuralRamsey.PartialSetStructure
