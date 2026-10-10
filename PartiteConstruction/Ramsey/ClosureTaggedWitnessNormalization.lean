import PartiteConstruction.Ramsey.ClosureTaggedLittlePicture
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-! # Normalizing a tagged recursive Ramsey witness

The recursive relative-copy theorem returns an arbitrary structure
in the root-tagged language. It is NOT legitimate to assume this
structure is the tagged expansion of its old-language reduct:
unary names may be missing, and original closure tuples may disagree
with the tagged closure-relation symbols.

A remedy is available for the ACTUAL recursive witness: it has a
closed-test protected map to the correctly normalized tagged expansion
of the little Picture, and its own tagged structure is U-tagged-closed.
The protected map is then an ordinary relational homomorphism-embedding.

Each existing relation tuple induces an ordinary irreducible seed on
its exact vertex range, and the homomorphism-embedding reflects all
relations on this range. It follows that old relation tuples and
their tagged versions have exactly the expected correspondence.
Unary part predicates are normalized using singleton support.

This gives literal equality of the source tagged structure with the
canonical expansion of its original-symbol reduct, with part labels
read from the projection. The old reduct is consequently U-closed.
No global injectivity or U-closedness of the projection TARGET is needed.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P X Y : Type v}

/-- The exact vertex range of any EXISTING relation tuple is ordinarily
irreducible. The result allows repeated and nullary entries and is
valid in an arbitrary relational signature. -/
theorem relationTuple_support_irreducible
    {M : RelLanguage.{max u v}}
    (A : RelStructure M X)
    (R : M.Symbol) (t : Fin (M.arity R) → X)
    (ht : A.rel R t) :
    (A.induce (Set.range t)).Irreducible := by
  intro x y hxy
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨j, hj⟩ := y.2
  let z : Fin (M.arity R) → Set.range t :=
    fun k => ⟨t k, ⟨k, rfl⟩⟩
  refine ⟨R, z, i, j, ?_, ?_, ?_⟩
  · exact ht
  · apply Subtype.ext
    exact hi
  · apply Subtype.ext
    exact hj

/-- The image of one unary coordinate is a singleton or empty and
hence irreducible regardless of whether ANY relation holds there. -/
theorem unaryTuple_support_irreducible
    {M : RelLanguage.{max u v}}
    (A : RelStructure M X) (t : Fin 1 → X) :
    (A.induce (Set.range t)).Irreducible := by
  intro x y hxy
  exfalso
  apply hxy
  apply Subtype.ext
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨j, hj⟩ := y.2
  have hij : i = j := Subsingleton.elim i j
  exact hi.symm.trans (by rw [hij]; exact hj)

/-- If a tagged structure maps homomorphism-embedding-wise to a
CANONICAL tagged expansion, then it must ITSELF be canonically
tagged by the part labels pulled back from that map.

The source need not be U-tagged-closed; the target need not be
U-closed. All that matters is the full reflection on each
ordinary irreducible tuple support, including singleton predicates. -/
theorem tagged_source_normalizes_of_homomorphismEmbedding
    (rules : ClosureDescription L)
    (T : RelStructure (L.withTaggedClosureParts rules P) X)
    (O : RelStructure L Y) (partO : Y → P) (f : X → Y)
    (hf : T.IsHomomorphismEmbedding
      (RelStructure.expandTaggedClosureParts rules O partO) f) :
    T = RelStructure.expandTaggedClosureParts rules
      (taggedOriginalReduct T) (partO ∘ f) := by
  let OT := RelStructure.expandTaggedClosureParts rules O partO
  let TN := RelStructure.expandTaggedClosureParts rules
    (taggedOriginalReduct T) (partO ∘ f)
  have hRel : T.rel = TN.rel := by
    funext sym z
    apply propext
    cases sym with
    | inl R =>
        rfl
    | inr sym =>
        cases sym with
        | inl tag =>
            constructor
            · intro ht
              have hIrred :=
                relationTuple_support_irreducible T (.inr (.inl tag)) z ht
              have hOTag : OT.rel (.inr (.inl tag)) (f ∘ z) :=
                hf.1 (.inr (.inl tag)) z ht
              have hOOld : OT.rel (.inl tag.rule.symbol) (f ∘ z) :=
                hOTag.1
              have hTOld : T.rel (.inl tag.rule.symbol) z :=
                hf.reflect_rel_on (Set.range z) hIrred (.inl tag.rule.symbol)
                  z (fun i => ⟨i, rfl⟩) hOOld
              exact ⟨hTOld, hOTag.2⟩
            · intro ht
              have hIrred :=
                relationTuple_support_irreducible T (.inl tag.rule.symbol) z ht.1
              have hOOld : OT.rel (.inl tag.rule.symbol) (f ∘ z) :=
                hf.1 (.inl tag.rule.symbol) z ht.1
              have hOTag : OT.rel (.inr (.inl tag)) (f ∘ z) :=
                ⟨hOOld, ht.2⟩
              exact hf.reflect_rel_on (Set.range z) hIrred
                (.inr (.inl tag)) z (fun i => ⟨i, rfl⟩) hOTag
        | inr p =>
            constructor
            · intro ht
              exact hf.1 (.inr (.inr p)) z ht
            · intro ht
              have hIrred : (T.induce (Set.range z)).Irreducible :=
                unaryTuple_support_irreducible T z
              exact hf.reflect_rel_on (Set.range z) hIrred
                (.inr (.inr p)) z (fun i => ⟨i, rfl⟩) ht
  exact congrArg (fun rel =>
    (RelStructure.mk rel :
      RelStructure (L.withTaggedClosureParts rules P) X)) hRel

/-- A U-tagged-CLOSED source and protected closed-test map are
sufficient to normalize the entire source, since protection implies
ordinary homomorphism-embedding on a closed source. -/
theorem tagged_closed_source_normalizes_of_protected
    (rules : ClosureDescription L)
    (T : RelStructure (L.withTaggedClosureParts rules P) X)
    (O : RelStructure L Y) (partO : Y → P) (f : X → Y)
    (hT : IsUClosed (rules.withTaggedClosureParts P) T)
    (hf : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T (RelStructure.expandTaggedClosureParts rules O partO) f) :
    T = RelStructure.expandTaggedClosureParts rules
      (taggedOriginalReduct T) (partO ∘ f) :=
  tagged_source_normalizes_of_homomorphismEmbedding
    rules T O partO f (hf.toHomomorphismEmbedding_of_closed hT)

/-- In particular the OLD relational reduct of the actual recursive
tagged witness is U-closed, even though the little Picture O need not
be U-semi-closed, because the source itself is normalized and tagged
U-closed. No K-completion assumptions or hull-size changes. -/
theorem tagged_closed_reduct_of_protected
    (rules : ClosureDescription L)
    (T : RelStructure (L.withTaggedClosureParts rules P) X)
    (O : RelStructure L Y) (partO : Y → P) (f : X → Y)
    (hT : IsUClosed (rules.withTaggedClosureParts P) T)
    (hf : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T (RelStructure.expandTaggedClosureParts rules O partO) f) :
    IsUClosed rules (taggedOriginalReduct T) := by
  apply (isUClosed_iff_taggedParts rules (taggedOriginalReduct T)
    (partO ∘ f)).mpr
  rw [← tagged_closed_source_normalizes_of_protected
    rules T O partO f hT hf]
  exact hT

end StructuralRamsey.RelStructure
