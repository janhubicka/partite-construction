import PartiteConstruction.Functional.WholeMaskCoveredTargetDomains2019
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Every OLD active complete-mask domain root is injective in a covered target

Canonical genuine partial function graphs require the distinct-input
root coordinates in an active OLD domain tuple to be pairwise distinct.
U-closedness alone does not forbid an arbitrary tagged target from
containing a collapsed domain tuple.

In the FINAL 2019 target, protected closed U-irreducible canonical B-copy
coverage fixes the issue. The active OLD domain tuple makes its exact
vertex support ordinary irreducible, so that exact weak support embeds
FULLY into canonical B. The OLD domain relation in B includes injectivity
of its root tuple, and full reflection gives injectivity in the target.

This is separate from complete-output graph validity and from the
consistent-part-set lemma already proved in covered-target domains.
No closure vertex is inserted into any weak source test.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- All active OLD domain roots, including ZERO-output masks and
nullary primitive function roots, are injective in a U-closed final
target protected by full canonical B-copy coverage. -/
theorem wholeMask_activeDomain_injective_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (root : Fin p.rootSize → V)
    (hDomain : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q))) root) :
    Function.Injective root := by
  classical
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q)))) root hDomain
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let rootS : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hB : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inl (p,q))) (g ∘ rootS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rootS).mpr hDomain
  intro i j hij
  apply hB.1
  apply congrArg g
  exact Subtype.ext hij

end StructuralRamsey.RelStructure
