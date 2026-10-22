import PartiteConstruction.Functional.WholeMaskPartialDecode2019
import PartiteConstruction.Functional.WholeMaskPositiveDomainCompletion2019
import PartiteConstruction.Functional.WholeMaskCoveredDefinedEmpty2019

/-!
# OLD domain existence: from active masks to complete Option(Set) values

The new OLD complete-mask language keeps the independent partial
definedness bit. A nonempty output-part mask is completed using the
fresh 2019 U-closure rule at its FULL positive injective root;
a zero-output mask is covered by the independent exact B-copy lemma
and must not be confused with undefinedness.

For positive primitive function arities, every surjective equality
pattern has a NONEMPTY distinct-input root. Consequently these two
cases exhaust the complete OLD domain masks, even when primitive
input arguments repeat or the value set is multivalued.

This module first states the exact active-root-injectivity hypothesis
explicitly. The final protected B-copy coverage proves that condition
separately; the complete downstream theorem will discharge it there.
No weak test/source projected image is replaced by a closure hull.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Every active OLD domain mask of a positive-arity primitive
function has a complete OLD value witness, provided each active
distinct-input root is injective and positive masks are completed
by the 2019 full-root closure rule. Zero masks use protected B-copy
reflection. This gives genuine definedness without any arbitrary
choice of output vertices or closure enlargement of the source. -/
theorem WholeMaskTagNormal.domain_has_wholeMaskValue_of_injective
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hNormal : WholeMaskTagNormal C)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hRootInj : ∀ (p : Language.FunctionInputPattern L)
      (q : Language.CompleteOutputParts P)
      (root : Fin p.rootSize → V),
      (wholeMaskTagReduct C).rel
        (.inr (.inl (p,q))) root →
      Function.Injective root)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (hDom : HasWholeMaskDomain (wholeMaskTagReduct C) F x) :
    ∃ U : Set V,
      HasWholeMaskValue (wholeMaskTagReduct C) F x U := by
  classical
  obtain ⟨m, r, hr, q, root, hActive, hArgs⟩ := hDom
  let pat : Language.FunctionInputPattern L :=
    ⟨F, m, r, hr⟩
  have hInj : Function.Injective root :=
    hRootInj pat q root hActive
  have hmPos : 0 < m := by
    by_contra h
    have hZero : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact Fin.elim0 (r ⟨0, hPos F⟩)
  by_cases hq0 : q.size = 0
  · obtain ⟨t, hGraph, hRoot⟩ :=
      wholeMask_definedEmpty_has_completeGraph_of_closed_coverage
        C Base part hClosed hCover pat q hq0 root hActive
    refine ⟨Set.range (fun j : Fin q.size =>
      t (Fin.natAdd m j)), m, r, hr, q, t, hGraph, ?_, rfl⟩
    intro i
    calc
      x i = root (r i) := hArgs i
      _ = t (Fin.castAdd q.size (r i)) := (hRoot (r i)).symm
  · have hqPos : 0 < q.size := Nat.pos_of_ne_zero hq0
    obtain ⟨t, hGraph, hRoot⟩ :=
      hNormal.positiveDomain_has_completeValue
        C hClosed pat q hmPos hqPos root hInj hActive
    refine ⟨Set.range (fun j : Fin q.size =>
      t (Fin.natAdd m j)), m, r, hr, q, t, hGraph, ?_, rfl⟩
    intro i
    calc
      x i = root (r i) := hArgs i
      _ = t (Fin.castAdd q.size (r i)) := (hRoot (r i)).symm

end StructuralRamsey.RelStructure
