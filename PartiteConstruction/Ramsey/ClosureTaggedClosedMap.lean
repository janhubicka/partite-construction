import PartiteConstruction.Ramsey.ClosureTaggedPositive
import PartiteConstruction.Ramsey.ClosureClosedMap

/-! # Protected closed-test maps across root-tagged part expansions

A positive map between tagged expansions is a protected closed-U-test
homomorphism-embedding iff its underlying old-language map protects
closed-U-irreducible tests and it preserves every part label.

The difficult direction concerns an ARBITRARY tagged-language closed
irreducible test embedded in the source. Normalize this test to the
tagged expansion of its original-symbol reduct using the full source
embedding, transport closedness and irreducibility by the previous
tagged equivalences, apply the original protected map, and expand the
resulting induced embedding back to the tagged language.

No new global injectivity, closedness of the source or target, and no
extra closedness of a weak exact test are assumed. This is precisely
the corrected map predicate, NOT the unrestricted literal 2019 map
whose tests may be intrinsically irreducible but nonclosed.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P U W : Type v}

/-- Precise map-transport theorem for the corrected closed-test notion.
The source and target may be nonclosed. Tagged unary part symbols force
the additional part-label equation; conversely that equation and the
old protected map suffice for ALL embedded tagged closed tests. -/
theorem isClosedUHomomorphismEmbedding_tagged_iff
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L W)
    (partA : U → P) (partB : W → P) (f : U → W) :
    IsClosedUHomomorphismEmbedding
        (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A partA)
        (RelStructure.expandTaggedClosureParts rules B partB) f ↔
      IsClosedUHomomorphismEmbedding rules A B f ∧
        (∀ x, partB (f x) = partA x) := by
  constructor
  · intro hTagged
    have hPart : ∀ x, partB (f x) = partA x :=
      hTagged.1.tagged_preserves_part
    refine ⟨⟨hTagged.1.forgetTaggedClosureParts, ?_⟩, hPart⟩
    intro E Test hClosed hIrred e
    let partTest : E → P := fun x => partA (e x)
    let eTag : Embedding
        (RelStructure.expandTaggedClosureParts rules Test partTest)
        (RelStructure.expandTaggedClosureParts rules A partA) :=
      e.expandTaggedClosureParts partTest partA (fun _ => rfl)
    have hClosedTag : IsUClosed (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules Test partTest) :=
      (isUClosed_iff_taggedParts rules Test partTest).mp hClosed
    have hIrredTag : IsUIrreducible (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules Test partTest) :=
      (isUIrreducible_iff_taggedParts_of_closed rules Test partTest hClosed).mp hIrred
    obtain ⟨g, hg⟩ := hTagged.on_test
      (RelStructure.expandTaggedClosureParts rules Test partTest)
      hClosedTag hIrredTag eTag
    exact ⟨g.forgetTaggedClosureParts, hg⟩
  · rintro ⟨hOld, hPart⟩
    refine ⟨hOld.1.expandTaggedClosureParts hPart, ?_⟩
    intro E Test hClosed hIrred eTag
    let Red : RelStructure L E := taggedOriginalReduct Test
    let partTest : E → P := fun x => partA (eTag x)
    have hNormal : Test = RelStructure.expandTaggedClosureParts rules Red partTest :=
      tagged_embedded_test_eq_expansion A partA Test eTag
    have hClosedRed : IsUClosed rules Red := by
      apply (isUClosed_iff_taggedParts rules Red partTest).mpr
      rw [← hNormal]
      exact hClosed
    have hIrredRed : IsUIrreducible rules Red := by
      apply (isUIrreducible_iff_taggedParts_of_closed
        rules Red partTest hClosedRed).mpr
      rw [← hNormal]
      exact hIrred
    let eOld : Embedding Red A := {
      toFun := eTag
      injective := eTag.injective
      map_rel_iff := fun R z => eTag.map_rel_iff (.inl R) z
    }
    obtain ⟨gOld, hg⟩ := hOld.on_test Red hClosedRed hIrredRed eOld
    have hGPart (x : E) : partB (gOld x) = partTest x := by
      rw [hg x]
      exact hPart (eTag x)
    let gTag : Embedding
        (RelStructure.expandTaggedClosureParts rules Red partTest)
        (RelStructure.expandTaggedClosureParts rules B partB) :=
      gOld.expandTaggedClosureParts partTest partB hGPart
    let gTest : Embedding Test
        (RelStructure.expandTaggedClosureParts rules B partB) := {
      toFun := gOld
      injective := gOld.injective
      map_rel_iff := by
        intro R z
        have hRel :
            (RelStructure.expandTaggedClosureParts rules Red partTest).rel R z ↔
              Test.rel R z := by
          rw [hNormal]
        exact (gTag.map_rel_iff R z).trans hRel
    }
    exact ⟨gTest, hg⟩

end StructuralRamsey.RelStructure
