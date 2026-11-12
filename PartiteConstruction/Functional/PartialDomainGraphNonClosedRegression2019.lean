import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Functional.PartialWeakCompleteDomainGraphIff2019

/-!
# Track A adversarial regression: induced domain/output graph embeddings
# need not be full functional embeddings

The existing two-output transversal, part-saturated Track A example
has a one-vertex weak cut S with no entirely lost defined applications.
Its complete induced ambient domain/output graph therefore agrees with
the graph of the intrinsic CLIPPED weak structure on the exact S.

The inclusion S → Fin 2 is an honest induced domain/output relational
embedding, but its vertex image is not function-closed: a value contains
another vertex outside S. Consequently it cannot be the underlying map
of any full genuinely partial-function embedding. This disproves the
tempting removal of the closed-range hypothesis from the positive
theorem; it does NOT challenge the canonical ambient OLD-mask semantics.
-/

namespace StructuralRamsey.FunctionalPartite.TrackASaturation

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

/-- A genuine induced embedding of independent domain and output
relations on a part-saturated transversal weak cut, with the
literal vertex inclusion as its underlying function. -/
def weakCutDomainGraphEmbedding :
    RelStructure.Embedding
      (PartialSetStructure.domainGraph (examplePartial.weakInduce S))
      (PartialSetStructure.domainGraph examplePartial) where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := by
    intro R xs
    change ((PartialSetStructure.domainGraph examplePartial).induce S).rel R xs ↔
      (PartialSetStructure.domainGraph (examplePartial.weakInduce S)).rel R xs
    exact ((clippedDomainGraph_agrees_iff_noLost
      examplePartial S).mpr noLost_even_though_not_closed.1 R xs).symm

/-- The image is exactly the originally chosen weak carrier,
not a larger closure hull. -/
theorem weakCutDomainGraphEmbedding_range_eq :
    Set.range weakCutDomainGraphEmbedding.toFun = S := by
  ext y
  constructor
  · rintro ⟨x, hxy⟩
    change x.1 = y at hxy
    exact hxy ▸ x.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- Domain/output inducedness and part-saturation do NOT imply
function-closed image for arbitrary multi-output operations. -/
theorem weakCutDomainGraphEmbedding_notClosed :
    ¬ examplePartial.IsClosed
      (Set.range weakCutDomainGraphEmbedding.toFun) := by
  rw [weakCutDomainGraphEmbedding_range_eq]
  exact noLost_even_though_not_closed.2

/-- The same map cannot be a full functional embedding. The obstruction
is exactly the extra function output, not a failed relation or domain bit. -/
theorem weakCutDomainGraphEmbedding_notFull :
    ¬ ∃ e : PartialSetStructure.Embedding
      (examplePartial.weakInduce S) examplePartial,
        e.toFun = weakCutDomainGraphEmbedding.toFun := by
  rintro ⟨e, he⟩
  have hClosed : examplePartial.IsClosed
      (Set.range weakCutDomainGraphEmbedding.toFun) := by
    simpa only [he] using e.range_isClosed
  exact weakCutDomainGraphEmbedding_notClosed hClosed

end StructuralRamsey.FunctionalPartite.TrackASaturation
