import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Functional.PartialDomainGraphCanonicalImage2019

/-!
# Track A: fully faithful canonical partial-function graph embeddings on closed images

The `Dom_F` and `Graph_F` representation of genuinely partial
`Option (Set V)` functions is faithful only on CANONICAL relational objects:
every positive output incidence must come from a defined input. Canonicality
is the exact image condition proven earlier in Track A.

Here we work directly with arbitrary canonical relational structures
`R`, `T` in this two-relation language, not graphs presented in advance
as actual partial functions. The source/target are decoded *on the same
vertex types*.

A relational induced embedding of `R` into `T` whose image is closed
under the decoded target's functions reconstructs a genuine FULL
partial-function embedding, with the exact same underlying map.
Conversely every full embedding of the decoded partial structures
induces the canonical relational embedding, and has closed image.

The independent domain predicate is necessary; using only output-graph
incidences would lose `some ∅` versus `none`. The closed-image condition
is also necessary, even in part-saturated transversal partite systems.

No completion theorem for arbitrary U-closed targets, no generated
closure hull, and no strict functional mixed-root B-tree is asserted.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Transfer a relational induced embedding of two CANONICAL independent
domain/output graphs to a FULL embedding of the decoded genuine partial
functions, when the literal vertex image is function-closed. -/
noncomputable def decodeClosedGraphEmbedding
    (R : RelStructure (domainGraphLanguage L) V)
    (T : RelStructure (domainGraphLanguage L) W)
    (hR : IsCanonicalDomainGraph R)
    (hT : IsCanonicalDomainGraph T)
    (g : RelStructure.Embedding R T)
    (hClosed : (decodeDomainGraph T).IsClosed (Set.range g.toFun)) :
    Embedding (decodeDomainGraph R) (decodeDomainGraph T) := by
  let gr : RelStructure.Embedding
      (domainGraph (decodeDomainGraph R))
      (domainGraph (decodeDomainGraph T)) := {
    toFun := g.toFun
    injective := g.injective
    map_rel_iff := by
      intro symbol xs
      rw [domainGraph_decode R hR, domainGraph_decode T hT]
      exact g.map_rel_iff symbol xs
  }
  exact Embedding.ofDomainGraphNoExtra gr
    (noExtra_of_domainGraphEmbedding_closed gr hClosed)

/-- The decoder does not change the vertex map or replace its range
by a generated closure. -/
theorem decodeClosedGraphEmbedding_toFun
    (R : RelStructure (domainGraphLanguage L) V)
    (T : RelStructure (domainGraphLanguage L) W)
    (hR : IsCanonicalDomainGraph R)
    (hT : IsCanonicalDomainGraph T)
    (g : RelStructure.Embedding R T)
    (hClosed : (decodeDomainGraph T).IsClosed (Set.range g.toFun)) :
    (decodeClosedGraphEmbedding R T hR hT g hClosed).toFun = g.toFun := by
  rfl

/-- Conversely, a full embedding of canonical decoded structures gives
an induced relational graph embedding, not merely a positive graph map. -/
noncomputable def encodeFullDecodedEmbedding
    (R : RelStructure (domainGraphLanguage L) V)
    (T : RelStructure (domainGraphLanguage L) W)
    (hR : IsCanonicalDomainGraph R)
    (hT : IsCanonicalDomainGraph T)
    (e : Embedding (decodeDomainGraph R) (decodeDomainGraph T)) :
    RelStructure.Embedding R T where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro symbol xs
    have h :
        (domainGraph (decodeDomainGraph T)).rel symbol
            (e.toFun ∘ xs) ↔
          (domainGraph (decodeDomainGraph R)).rel symbol xs :=
      e.domainGraph.map_rel_iff symbol xs
    exact (domainGraph_decode_rel_iff T hT symbol
      (e.toFun ∘ xs)).symm.trans
        (h.trans (domainGraph_decode_rel_iff R hR symbol xs))

/-- The reverse direction likewise preserves the underlying vertex map. -/
theorem encodeFullDecodedEmbedding_toFun
    (R : RelStructure (domainGraphLanguage L) V)
    (T : RelStructure (domainGraphLanguage L) W)
    (hR : IsCanonicalDomainGraph R)
    (hT : IsCanonicalDomainGraph T)
    (e : Embedding (decodeDomainGraph R) (decodeDomainGraph T)) :
    (encodeFullDecodedEmbedding R T hR hT e).toFun = e.toFun := by
  rfl

/-- Precise SAME-CARRIER and SAME-MAP equivalence for the full-embedding
part of the canonical domain/output relationalization. This theorem is
not yet the survey's local completion or sparsening theorem. -/
theorem canonicalClosedGraphEmbedding_iff_fullDecodedEmbedding
    (R : RelStructure (domainGraphLanguage L) V)
    (T : RelStructure (domainGraphLanguage L) W)
    (hR : IsCanonicalDomainGraph R)
    (hT : IsCanonicalDomainGraph T)
    (f : V → W) :
    ((∃ g : RelStructure.Embedding R T, g.toFun = f) ∧
      (decodeDomainGraph T).IsClosed (Set.range f)) ↔
      (∃ e : Embedding (decodeDomainGraph R) (decodeDomainGraph T),
        e.toFun = f) := by
  constructor
  · rintro ⟨⟨g, hg⟩, hClosed⟩
    subst f
    exact ⟨decodeClosedGraphEmbedding R T hR hT g hClosed,
      decodeClosedGraphEmbedding_toFun R T hR hT g hClosed⟩
  · rintro ⟨e, he⟩
    subst f
    refine ⟨⟨encodeFullDecodedEmbedding R T hR hT e,
        encodeFullDecodedEmbedding_toFun R T hR hT e⟩, ?_⟩
    exact e.range_isClosed

end StructuralRamsey.PartialSetStructure
