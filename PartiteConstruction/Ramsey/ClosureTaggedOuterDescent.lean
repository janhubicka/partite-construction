import PartiteConstruction.Ramsey.ClosureTaggedWitnessNormalization
import PartiteConstruction.Partite.InducedAttachment

/-! # Descent from the normalized tagged witness to an outer partite system

A tagged-language HE to the correctly normalized expansion of an old
structure forgets to an ordinary HE between the underlying old-language
structures. In particular, for the actual closed tagged recursive
witness, its protected projection to the temporarily conflicting little
Picture becomes an ordinary HE of the old reduct into that picture.

Composing with the old partite projection gives an ordinary HE into
the original ambient part structure D. This supplies both the old
outer partition and its transversality invariant.

Separately, the tagged Ramsey arrow is exactly the native selected-profile
PictureProperty whenever source and target are canonical expansions.
This file does not yet derive the stronger closed-test-protected outer
projection: that last step must use closed-test coverage by the OLD
picture, not the generally nonclosed little Picture.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P X Y : Type v}

/-- Forgetting the root-tagged symbols and unary predicates preserves
ordinary relational homomorphism-embeddings. The source need not be
normalized; the original relation symbols are literally retained. -/
theorem IsHomomorphismEmbedding.forgetTaggedOriginal
    (rules : ClosureDescription L)
    (T : RelStructure (L.withTaggedClosureParts rules P) X)
    (O : RelStructure L Y) (partO : Y → P) (f : X → Y)
    (hf : T.IsHomomorphismEmbedding
      (RelStructure.expandTaggedClosureParts rules O partO) f) :
    (taggedOriginalReduct T).IsHomomorphismEmbedding O f := by
  constructor
  · intro R z hz
    exact hf.1 (.inl R) z hz
  · intro S hIrred
    have hIrredTag : (T.induce S).Irreducible := by
      intro x y hxy
      obtain ⟨R, z, i, j, hz, hi, hj⟩ := hIrred hxy
      exact ⟨.inl R, z, i, j, hz, hi, hj⟩
    obtain ⟨g, hg⟩ := hf.embeddingOn S hIrredTag
    let gOld : Embedding ((taggedOriginalReduct T).induce S) O := {
      toFun := g
      injective := g.injective
      map_rel_iff := fun R z => g.map_rel_iff (.inl R) z
    }
    exact ⟨gOld, hg⟩

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}} {P Q V W Y : Type v}

/-- Reverse direction of the tagged-picture arrow equivalence:
a Ramsey copy of the old picture in the tagged expansion is precisely
a part-preserving copy, and every tagged A-subcopy corresponds to a
selected projected A-copy of the old partite system. -/
theorem pictureProperty_of_taggedArrow
    (rules : ClosureDescription L)
    (A : RelStructure L Q)
    (Old : System L P V) (alpha : Q ↪ P)
    (C : System L P W)
    (Color : Type*)
    (hArrow : StructuralRamsey.Arrow
      (RelStructure.expandTaggedClosureParts rules A alpha)
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part)
      (RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part)
      Color) :
    Partite.PictureProperty A Old alpha C Color := by
  let toProjected :
      RelStructure.Embedding
        (RelStructure.expandTaggedClosureParts rules A alpha)
        (RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part) →
      Partite.ProjectedEmbedding A C alpha :=
    fun e => ⟨e.forgetTaggedClosureParts, e.tagged_preserves_part⟩
  intro chi
  obtain ⟨fTag, hf⟩ := hArrow (fun e => chi (toProjected e))
  let f : Partite.Embedding Old C := {
    toEmbedding := fTag.forgetTaggedClosureParts
    map_part := fTag.tagged_preserves_part
  }
  refine ⟨f, ?_⟩
  intro a1 a2
  let a1Tag : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules A alpha)
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part) :=
    a1.val.expandTaggedClosureParts alpha Old.part a1.property
  let a2Tag : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules A alpha)
      (RelStructure.expandTaggedClosureParts rules Old.toRelStructure Old.part) :=
    a2.val.expandTaggedClosureParts alpha Old.part a2.property
  have h1 : toProjected (fTag.comp a1Tag) = a1.comp f := by
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have h2 : toProjected (fTag.comp a2Tag) = a2.comp f := by
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro x
    rfl
  calc
    chi (a1.comp f) = chi (toProjected (fTag.comp a1Tag)) :=
      congrArg chi h1.symm
    _ = chi (toProjected (fTag.comp a2Tag)) := hf a1Tag a2Tag
    _ = chi (a2.comp f) := congrArg chi h2

/-- Descend the tagged inner Ramsey witness to a genuine D-partite
system using the unique outer part map obtained by composing the
tagged projection into O with the existing O-to-D part projection.

This does not assume a global injective part map; injectivity is
proved only on relation-tuple supports, using the ordinary HE and the
transversality of D-partite O. -/
noncomputable def taggedWitnessOuterSystem
    (rules : ClosureDescription L)
    (D : RelStructure L P) (O : System L P W)
    (T : System (L.withTaggedClosureParts rules P) W Y)
    (hTO : IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure)
    (hProj : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T.toRelStructure
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      T.part)
    (hOPart : O.IsPartiteOver D) :
    System L P Y := by
  let Red := taggedOriginalReduct T.toRelStructure
  let p : Y → P := O.part ∘ T.part
  have hHEtag : T.toRelStructure.IsHomomorphismEmbedding
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part) T.part :=
    hProj.toHomomorphismEmbedding_of_closed hTO
  have hHEold : Red.IsHomomorphismEmbedding O.toRelStructure T.part :=
    hHEtag.forgetTaggedOriginal rules T.toRelStructure O.toRelStructure
      O.part T.part
  have hOuter : Red.IsHomomorphismEmbedding D p :=
    hOPart.comp hHEold
  exact {
    toRelStructure := Red
    part := p
    transversal := by
      intro R z hz i j hp
      let S : Set Y := Set.range z
      have hIrred : (Red.induce S).Irreducible := by
        intro x y hxy
        obtain ⟨i0, hi0⟩ := x.2
        obtain ⟨j0, hj0⟩ := y.2
        let t : Fin (L.arity R) → S :=
          fun k => ⟨z k, ⟨k, rfl⟩⟩
        refine ⟨R, t, i0, j0, ?_, ?_, ?_⟩
        · exact hz
        · apply Subtype.ext
          exact hi0
        · apply Subtype.ext
          exact hj0
      exact hOuter.injOn S hIrred ⟨i, rfl⟩ ⟨j, rfl⟩ hp
  }

/-- The outer system obtained from a closed tagged witness is genuinely
U-closed in the ORIGINAL relational language, even when O is not. -/
theorem taggedWitnessOuterSystem_isUClosed
    (rules : ClosureDescription L)
    (D : RelStructure L P) (O : System L P W)
    (T : System (L.withTaggedClosureParts rules P) W Y)
    (hTO : IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure)
    (hProj : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T.toRelStructure
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      T.part)
    (hOPart : O.IsPartiteOver D) :
    IsUClosed rules
      (taggedWitnessOuterSystem rules D O T hTO hProj hOPart).toRelStructure :=
  tagged_closed_reduct_of_protected rules T.toRelStructure
    O.toRelStructure O.part T.part hTO hProj

/-- The descended structure remains ordinarily D-partite, without
requiring global semi-closedness of O or any new source-image hull. -/
theorem taggedWitnessOuterSystem_isPartiteOver
    (rules : ClosureDescription L)
    (D : RelStructure L P) (O : System L P W)
    (T : System (L.withTaggedClosureParts rules P) W Y)
    (hTO : IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure)
    (hProj : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T.toRelStructure
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      T.part)
    (hOPart : O.IsPartiteOver D) :
    (taggedWitnessOuterSystem rules D O T hTO hProj hOPart).IsPartiteOver D := by
  have hHEtag := hProj.toHomomorphismEmbedding_of_closed hTO
  have hHEold : (taggedOriginalReduct T.toRelStructure).IsHomomorphismEmbedding
      O.toRelStructure T.part :=
    hHEtag.forgetTaggedOriginal rules T.toRelStructure O.toRelStructure O.part T.part
  exact hOPart.comp hHEold

end StructuralRamsey.Partite.Induced
