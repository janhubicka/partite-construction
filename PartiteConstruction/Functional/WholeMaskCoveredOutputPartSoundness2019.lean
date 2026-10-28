import PartiteConstruction.Functional.WholeMaskCoveredUnaryPart2019
import PartiteConstruction.Functional.WholeMaskDecodedOutputParts2019

/-!
# Decoded output vertices agree with their automatically recovered part map

The final U-closed tagged Picture is only a RELATIONAL object until
B-copy coverage supplies genuine partial function semantics. Its
unary input-part relations become a unique actual part map by
the singleton B-copy coverage lemma.

A complete OLD mask output relation also has an ordinarily
irreducible exact tuple support. Embedding that exact tuple carrier
FULLY into canonical B shows that each output vertex satisfies
the unary predicate naming its corresponding mask label.
The chosen unique part must therefore equal the declared label.

Hence the decoded Option(Set) outputs are transversal to the
recovered part map, with NO external part-coherence assumption.
This is a FINAL target normalization theorem, not an intermediate
profile-picture invariant. The tested weak carriers are unchanged.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- An OLD complete mask relation in a final protected picture
forces the indicated unary part predicate on EACH output vertex.
Unlike input-root closure, this holds even for defined-empty and
nullary functions (the output index case is vacuous when empty). -/
theorem wholeMask_output_part_predicate_of_closed_coverage
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (p : Language.FunctionInputPattern (L.withParts P))
    (q : Language.CompleteOutputParts P)
    (t : Fin (p.rootSize + q.size) → V)
    (ht : C.rel (.inl (.inr (.inr (p,q)))) t)
    (j : Fin q.size) :
    WholeMaskVertexPartHolds C
      (t (Fin.natAdd p.rootSize j)) (q.label j) := by
  classical
  let S : Set V := Set.range t
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C (.inl (.inr (.inr (p,q)))) t ht
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let ts : Fin (p.rootSize + q.size) → S :=
    fun k => ⟨t k, ⟨k,rfl⟩⟩
  have hB :
      ((Base.withParts basePart).wholeMaskPatternGraph basePart).rel
        (.inr (.inr (p,q))) (g ∘ ts) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) ts).mpr ht
  have hPartB : basePart (g (ts (Fin.natAdd p.rootSize j))) =
      q.label j := hB.2.2 j
  have hUnaryB :
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)).rel
          (.inl (.inl (.inr (q.label j))))
          (g ∘ (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j))) := by
    change basePart (g (ts (Fin.natAdd p.rootSize j))) = q.label j
    exact hPartB
  have hLocal : (C.induce S).rel (.inl (.inl (.inr (q.label j))))
      (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j)) :=
    (g.map_rel_iff (.inl (.inl (.inr (q.label j))))
      (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j))).mp hUnaryB
  exact hLocal

/-- In the protected closed picture, every OLD complete output
tuple respects the ACTUAL part map reconstructed from unary
relations. This discharges the extra output-label premise that
the generic Option(Set) decoder needed. -/
theorem wholeMask_outputPartsCompatible_of_closed_coverage
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) :
    WholeMaskOutputPartsCompatible (wholeMaskTagReduct C)
      (wholeMaskCoveredPart C Base basePart hC hCover) := by
  classical
  intro p q t ht j
  let x : V := t (Fin.natAdd p.rootSize j)
  let actualPart := wholeMaskCoveredPart C Base basePart hC hCover
  have hP : WholeMaskVertexPartHolds C x (q.label j) :=
    wholeMask_output_part_predicate_of_closed_coverage
      C Base basePart hC hCover p q t ht j
  have hUnique :=
    (Classical.choose_spec
      (wholeMask_vertexPart_existsUnique_of_closed_coverage
        C Base basePart hC hCover x)).2
  exact (hUnique (q.label j) hP).symm

/-- The final U-closed protected B-covered target decodes to a
genuinely partial structure with TRANSVERSAL output fibres,
automatically using the unique unary input-part labels.

No temporary tagged Picture is required to decode, and the
target actual part map is derived rather than assumed. -/
theorem wholeMaskCoveredPart_decoder_fibreTransversal
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) :
    PartialSetStructure.FibreTransversal
      ((wholeMaskTagReduct C).wholeMaskPartialDecode)
      (wholeMaskCoveredPart C Base basePart hC hCover) := by
  exact wholeMaskPartialDecode_fibreTransversal_of_closed_coverage
    C (Base.withParts basePart) basePart
    (wholeMaskCoveredPart C Base basePart hC hCover)
    hC (hPos.withParts) hCover
    (wholeMask_outputPartsCompatible_of_closed_coverage
      C Base basePart hC hCover)

end StructuralRamsey.RelStructure
