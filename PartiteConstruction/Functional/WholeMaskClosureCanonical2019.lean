import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019

/-!
# Canonical complete-value tagged sources are U-CLOSED (positive roots)

Every full OLD embedded input-root pattern whose domain mask is active
comes from a genuine defined value with exactly that set of output parts.
For each output part there is a unique vertex of that part in the value
set (existence by the mask-domain predicate, uniqueness by transversality).
Consequently the complete output tuple exists and is unique over the root.

Combined with the verified U-semi-closed source theorem, this supplies
exactly the 2019 U-closedness of the canonical FULL-root tagged source for
positive input roots and nonempty output masks.

Defined-empty and nullary-root cases remain old-data/other reductions.
This does not decode arbitrary U-closed target Pictures or settle the
strict functional mixed-step target completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- The canonical full-root tagged whole-value source is U-closed for
the positive-root, positive-output complete-mask closure description.
For each matching active root, every required output coordinate exists
by the ambient mask and is unique by transversality. -/
theorem wholeMaskTagExpansion_isUClosed
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part) :
    IsUClosed (L.wholeMaskClosureRules P)
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) := by
  classical
  apply (A.wholeMaskTagExpansion_isUSemiClosed part hTrans).isUClosed_of_exists
  intro rule hrule e
  obtain ⟨p, rfl⟩ := hrule
  let Old := A.wholeMaskPatternGraph part
  let old : Embedding p.root Old := e.wholeMaskTagReduct
  have hDomain : Old.rel (.inr (.inl (p.input, p.mask))) (old ∘ id) :=
    (old.map_rel_iff (.inr (.inl (p.input, p.mask))) id).mpr
      p.hasDomain
  have hDom :
      Function.Injective (old : Fin p.input.rootSize → V) ∧
        ∃ U : Set V,
          A.func p.input.symbol (old ∘ p.input.argMap) = some U ∧
          part '' U = Set.range p.mask.label := by
    simpa only [Old, wholeMaskPatternGraph, Function.comp_id] using hDomain
  obtain ⟨_, U, hValue, hMask⟩ := hDom
  have hExists (j : Fin p.mask.size) :
      ∃ y : V, y ∈ U ∧ part y = p.mask.label j := by
    have hPart : p.mask.label j ∈ part '' U := by
      rw [hMask]
      exact ⟨j, rfl⟩
    obtain ⟨y, hy, hp⟩ := hPart
    exact ⟨y, hy, hp⟩
  let output : Fin p.mask.size → V :=
    fun j => Classical.choose (hExists j)
  have hOutputMem (j : Fin p.mask.size) : output j ∈ U :=
    (Classical.choose_spec (hExists j)).1
  have hOutputPart (j : Fin p.mask.size) :
      part (output j) = p.mask.label j :=
    (Classical.choose_spec (hExists j)).2
  have hRange : Set.range output = U := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact hOutputMem j
    · intro hy
      have hPart : part y ∈ Set.range p.mask.label := by
        rw [← hMask]
        exact ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := hPart
      have heq : y = output j :=
        hTrans p.input.symbol (old ∘ p.input.argMap)
          U hValue y hy (output j) (hOutputMem j)
          (hj.symm.trans (hOutputPart j).symm)
      exact ⟨j, heq.symm⟩
  let t : Fin (p.input.rootSize + p.mask.size) → V :=
    Fin.append old output
  have hGraph : Old.rel (.inr (.inr (p.input, p.mask))) t := by
    change
      Function.Injective
        (fun i : Fin p.input.rootSize =>
          t (Fin.castAdd p.mask.size i)) ∧
      A.func p.input.symbol
        ((fun i : Fin p.input.rootSize =>
          t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap) =
          some (Set.range (fun j : Fin p.mask.size =>
            t (Fin.natAdd p.input.rootSize j))) ∧
      (∀ j : Fin p.mask.size,
        part (t (Fin.natAdd p.input.rootSize j)) = p.mask.label j)
    simp only [t, Fin.append_left, Fin.append_right]
    exact ⟨old.injective, by rw [hRange]; exact hValue, hOutputPart⟩
  have hTag : (wholeMaskTagExpansion Old).rel (.inr p) t := by
    change
      Old.rel (.inr (.inr (p.input, p.mask))) t ∧
        ∃ g : Embedding p.root Old,
          ∀ i : Fin p.input.rootSize,
            t (Fin.castAdd p.mask.size i) = g i
    refine ⟨hGraph, old, ?_⟩
    intro i
    exact Fin.append_left old output i
  refine ⟨t, ⟨hTag, ?_⟩⟩
  intro i
  have hIdx :
      i.castLE p.closureRule.rootLE =
        Fin.castAdd p.mask.size i := by
    apply Fin.ext
    rfl
  rw [hIdx]
  exact Fin.append_left old output i

end StructuralRamsey.PartialSetStructure
