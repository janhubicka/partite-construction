import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# Nonclosed attaching supports make native REST ranges non-U-closed

The temporarily conflicting little Picture used in the repaired
Lemma 2.28 attaches old copies along an exact part restriction S,
which may NOT be relatively U-closed in the old U-closed picture.

Even though every SELECTED embedded U-closed test in the core has
a relatively U-closed range (#185), it does NOT follow that the
ENTIRE core or the complementary rest of a selected copy is a
relative U-substructure of the whole little Picture.

This is a general obstruction independent of the chosen HJ line
family: if some old closure tuple has all designated root vertices
in S but an output outside S, its tuple in the attached copy has
all roots in the central core and an output in that copy's
private exterior. Thus BOTH the whole core range and the
literal rest-of-copy vertex set violate relative U-closedness.

Consequently the free-cover pullback theorem on PR #236 must
not be applied directly to the native copy/rest cut without first
establishing relative closure for the particular *tested image*.
The obstruction does not invalidate the already proved relative
closure of individual selected-profile CLOSED copies: those
tests may avoid the competing exterior tuples.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v w z
variable {L : RelLanguage.{u}}
variable {V : Type v} {W : Type w} {I : Type z}

variable (Old : RelStructure L V) (S : Set V)
variable (Core : RelStructure L W)
variable (maps : I → Embedding (Old.induce S) Core)

/-- A genuine closure tuple of Old leaving the attaching support
makes the ENTIRE core range non-relative-U-closed in the actual
attachment. No U-closedness or semi-closedness premise is needed
on Old or Core; no choice of the attaching embeddings can fix it. -/
theorem core_range_not_USubstructure_of_nonclosed_support
    {rules : ClosureDescription L}
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → V)
    (ht : Old.rel rule.symbol t)
    (hRootS : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) ∈ S)
    (j : Fin (L.arity rule.symbol)) (hOutside : t j ∉ S)
    (i : I) :
    ¬ IsUSubstructure rules
      (attach Old S Core maps)
      (Set.range (coreEmbedding Old S Core maps)) := by
  intro hRel
  let tc : Fin (L.arity rule.symbol) →
      Vertex S (W := W) (I := I) :=
    fun k => copyMap Old S Core maps i (t k)
  have htAtt : (attach Old S Core maps).rel rule.symbol tc :=
    ((copyEmbedding Old S Core maps i).map_rel_iff rule.symbol t).mpr ht
  have hRoots : ∀ k : Fin rule.rootSize,
      tc (k.castLE rule.rootLE) ∈
        Set.range (coreEmbedding Old S Core maps) := by
    intro k
    refine ⟨maps i ⟨t (k.castLE rule.rootLE), hRootS k⟩, ?_⟩
    exact (copyMap_mem i (t (k.castLE rule.rootLE)) (hRootS k)).symm
  obtain ⟨w, hw⟩ := hRel rule hrule tc htAtt hRoots j
  have hout : tc j =
      Sum.inr (i, (⟨t j, hOutside⟩ : {x : V // x ∉ S})) :=
    copyMap_not_mem i (t j) hOutside
  have hcore : tc j = Sum.inl w := hw.symm
  rw [hout] at hcore
  cases hcore

/-- More specifically, the REST of one attached copy (all vertices
except that copy's private exterior) is NOT relatively U-closed
when the old attaching support omits an output of a prescribed root.
This directly limits the use of generic inverse-image closed
free-cover lemmas in a non-semi-closed HJ little Picture. -/
theorem rest_not_USubstructure_of_nonclosed_support
    {rules : ClosureDescription L}
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → V)
    (ht : Old.rel rule.symbol t)
    (hRootS : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) ∈ S)
    (j : Fin (L.arity rule.symbol)) (hOutside : t j ∉ S)
    (i : I) :
    ¬ IsUSubstructure rules
      (attach Old S Core maps)
      {z : Vertex S (W := W) (I := I) |
        ¬ OutsideAt (W := W) (I := I) S i z} := by
  intro hRel
  let tc : Fin (L.arity rule.symbol) →
      Vertex S (W := W) (I := I) :=
    fun k => copyMap Old S Core maps i (t k)
  have htAtt : (attach Old S Core maps).rel rule.symbol tc :=
    ((copyEmbedding Old S Core maps i).map_rel_iff rule.symbol t).mpr ht
  have hRoots : ∀ k : Fin rule.rootSize,
      ¬ OutsideAt (W := W) (I := I) S i
        (tc (k.castLE rule.rootLE)) := by
    intro k
    rw [show tc (k.castLE rule.rootLE) =
        Sum.inl (maps i ⟨t (k.castLE rule.rootLE), hRootS k⟩) from
      copyMap_mem i (t (k.castLE rule.rootLE)) (hRootS k)]
    rintro ⟨x, hx⟩
    cases hx
  have hOutRest := hRel rule hrule tc htAtt hRoots j
  apply hOutRest
  refine ⟨⟨t j, hOutside⟩, ?_⟩
  exact copyMap_not_mem i (t j) hOutside

end StructuralRamsey.RelStructure.Attachment
