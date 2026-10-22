import PartiteConstruction.Functional.WholeMaskCoveredTargetDomains2019
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Defined-empty domains in a final covered OLD function graph

The syntactic domain relation with an output mask of size zero is
different from an undefined primitive operation. In canonical genuine
partial functions, a zero-mask active domain forces the complete
output value to be some EMPTY SET, so the corresponding complete
zero-output graph tuple holds on precisely the input-root vertices.

An arbitrary tagged U-closed target need not have that property.
But final protected closed U-irreducible B-copy coverage forces it:
the active domain relation makes its exact input-root support ordinary
irreducible; embed this support FULLY in canonical B, use B's genuine
partial-function semantics, and reflect the zero-output tuple.

No positivity assumption on the input arity and no added vertices are
needed. This is independent of the positive-output fresh U-tags.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- A zero-output part mask has no indices, hence no entries or
part labels. This is distinct from saying the function is undefined. -/
theorem completeOutputParts_zero_no_index
    (q : Language.CompleteOutputParts P) (hq : q.size = 0)
    (j : Fin q.size) : False := by
  have j0 : Fin 0 := hq ▸ j
  exact Fin.elim0 j0

/-- Under final B-copy coverage, an active OLD zero-output mask
forces an actual complete EMPTY-value graph tuple on the EXACT
same root vertices. In particular the old domain bit is not silently
discarded when a defined value has no output vertices. -/
theorem wholeMask_definedEmpty_has_completeGraph_of_closed_coverage
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
    (hq : q.size = 0)
    (root : Fin p.rootSize → V)
    (hDom : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q))) root) :
    ∃ t : Fin (p.rootSize + q.size) → V,
      (wholeMaskTagReduct C).rel (.inr (.inr (p,q))) t ∧
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd q.size i) = root i := by
  classical
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q)))) root hDom
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let rootS : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hDomB : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inl (p,q))) (g ∘ rootS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rootS).mpr hDom
  obtain ⟨hInjB, U, hValueB, hMaskB⟩ := hDomB
  have hMaskEmpty : Set.range q.label = (∅ : Set P) := by
    ext a
    constructor
    · rintro ⟨j, _⟩
      exact False.elim (completeOutputParts_zero_no_index q hq j)
    · intro ha
      exact ha.elim
  have hUEmpty : U = ∅ := by
    ext y
    constructor
    · intro hy
      have hPart : part y ∈ Set.range q.label := by
        rw [← hMaskB]
        exact ⟨y, hy, rfl⟩
      rw [hMaskEmpty] at hPart
      exact hPart.elim
    · intro hy
      exact hy.elim
  have hValueEmpty :
      Base.func p.symbol ((g ∘ rootS) ∘ p.argMap) = some (∅ : Set W) := by
    rw [hUEmpty] at hValueB
    exact hValueB
  let tS : Fin (p.rootSize + q.size) → S :=
    Fin.append rootS
      (fun j : Fin q.size =>
        False.elim (completeOutputParts_zero_no_index q hq j))
  have hInput : (fun i : Fin p.rootSize =>
      (g ∘ tS) (Fin.castAdd q.size i)) = g ∘ rootS := by
    funext i
    rfl
  have hOutputEmpty : Set.range (fun j : Fin q.size =>
      (g ∘ tS) (Fin.natAdd p.rootSize j)) = (∅ : Set W) := by
    ext y
    constructor
    · rintro ⟨j, _⟩
      exact False.elim (completeOutputParts_zero_no_index q hq j)
    · intro hy
      exact hy.elim
  have hGraphB : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p,q))) (g ∘ tS) := by
    change Function.Injective (fun i : Fin p.rootSize =>
        (g ∘ tS) (Fin.castAdd q.size i)) ∧
      Base.func p.symbol
        ((fun i : Fin p.rootSize =>
          (g ∘ tS) (Fin.castAdd q.size i)) ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          (g ∘ tS) (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin q.size,
        part ((g ∘ tS) (Fin.natAdd p.rootSize j)) = q.label j)
    constructor
    · rw [hInput]
      exact hInjB
    constructor
    · rw [hInput, hOutputEmpty]
      exact hValueEmpty
    · intro j
      exact False.elim (completeOutputParts_zero_no_index q hq j)
  have hLocal : (C.induce S).rel
      (.inl (.inr (.inr (p,q)))) tS :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) tS).mp hGraphB
  refine ⟨Subtype.val ∘ tS, hLocal, ?_⟩
  intro i
  rfl

end StructuralRamsey.RelStructure
