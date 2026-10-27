import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019
import PartiteConstruction.Functional.WholeMaskCanonicalPartialRoundTrip2019
import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019

/-!
# Full partite embeddings are exactly canonical OLD mask embeddings

For genuine partial Option(Set) functions, the complete OLD value/domain
language is faithful to FULL embeddings, including undefined versus
defined-empty. However its input part-map must not remain external:
isolated vertices can otherwise be reassigned to a different part.

First expand the source function LANGUAGE by unary part predicates,
then take its canonical OLD complete-mask representation. Every full
relational embedding of these canonical OLD graphs is precisely one
part-preserving full genuine partial-function embedding.

The proof uses the already validated forward complete-mask encoding
and reverse normalized-target decoder, the genuine partial-function
source round trip, and the checked equivalence for unary part
predicate expansion. The embedding correspondence is literally
identity on underlying vertex maps, so it is natural for composition.

This is a source/canonical-target equivalence. It does not assert an
arbitrary intermediate relational Picture is already a genuinely
partial-function structure. That decoding is performed only in the
final U-closed B-covered stage of the verified 2019 two-pass route.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V W : Type v}

/-- Encode actual vertex parts as unary SOURCE-language predicates
before taking complete OLD domain/value masks. The canonical
relational structure has exactly the original vertices. -/
def withPartsWholeMaskOld
    (A : PartialSetStructure L V) (part : V → P) :
    RelStructure ((L.withParts P).wholeMaskPatternLanguage P) V :=
  (A.withParts part).wholeMaskPatternGraph part

/-- Full partial-function embeddings preserving EVERY vertex part,
including isolated vertices. This is the appropriate embedding type
for genuine functional PARTITE Ramsey arrows. -/
abbrev PartPreservingEmbedding
    (A : PartialSetStructure L V) (partA : V → P)
    (B : PartialSetStructure L W) (partB : W → P) :=
  { e : Embedding A B //
    ∀ x : V, partB (e.toFun x) = partA x }

namespace PartPreservingEmbedding

variable {A : PartialSetStructure L V} {B : PartialSetStructure L W}
variable {partA : V → P} {partB : W → P}

/-- The canonical full OLD graph encoding of a full part-preserving
genuine partial function embedding, without changing the vertex map. -/
def encode
    (e : PartPreservingEmbedding A partA B partB) :
    RelStructure.Embedding
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB) :=
  (e.1.withParts partA partB e.2).wholeMaskPatternGraph
    partA partB (fun x => e.2 x)

/-- The full OLD domain and value relations on the expanded source
force one full partial-function embedding, even if a function is
defined-empty or undefined on a given primitive input. -/
noncomputable def decode
    [Finite V] [Finite W]
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (f : RelStructure.Embedding
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)) :
    PartPreservingEmbedding A partA B partB := by
  classical
  let Aplus := A.withParts partA
  let Bplus := B.withParts partB
  let Old := Bplus.wholeMaskPatternGraph partB
  have hATrans : FibreTransversal Aplus partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTransA
  have hBTrans : FibreTransversal Bplus partB :=
    (B.withParts_fibreTransversal_iff partB).mpr hTransB
  have hUnique (F : (L.withParts P).FuncSymbol)
      (xs : Fin ((L.withParts P).funcArity F) → W)
      (U T : Set W)
      (hU : HasWholeMaskValue Old F xs U)
      (hT : HasWholeMaskValue Old F xs T) : U = T := by
    have hu : Bplus.func F xs = some U :=
      (Bplus.hasWholeMaskValue_iff_source_func_some
        partB hBTrans F xs U).mp hU
    have ht : Bplus.func F xs = some T :=
      (Bplus.hasWholeMaskValue_iff_source_func_some
        partB hBTrans F xs T).mp hT
    exact Option.some.inj (hu.symm.trans ht)
  have hDomain (F : (L.withParts P).FuncSymbol)
      (xs : Fin ((L.withParts P).funcArity F) → W) :
      Old.wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain Old F xs := by
    have hd := Bplus.hasWholeMaskDomain_iff_sourceDefined
      partB hBTrans F xs
    change
      (∃ U : Set W,
        Old.wholeMaskPartialDecode.func F xs = some U) ↔ _
    rw [Bplus.wholeMaskPartialDecode_canonical_func
      partB hBTrans F xs]
    exact hd.symm
  let eD : Embedding Aplus Old.wholeMaskPartialDecode :=
    Embedding.ofWholeMaskPatternGraph
      Aplus partA hATrans Old hUnique hDomain f
  let eB : Embedding Aplus Bplus := {
    toFun := eD.toFun
    injective := eD.injective
    map_rel_iff := by
      intro R xs
      exact eD.map_rel_iff R xs
    map_func := by
      intro F xs
      have h := eD.map_func F xs
      change (Aplus.func F xs).map
        (Structure.imageSet eD.toFun) =
          Old.wholeMaskPartialDecode.func F (eD.toFun ∘ xs) at h
      rw [Bplus.wholeMaskPartialDecode_canonical_func
        partB hBTrans F (eD.toFun ∘ xs)] at h
      exact h
  }
  exact ⟨eB.forgetParts, eB.withParts_preserves_part partA partB⟩

/-- Embedding correspondence between genuine partial function PARTITE
copies and full induced embeddings of their unary-part-labelled OLD
complete-mask graphs. Both directions are literally the identity on
vertex maps; no vertices or values are added, and no part label may be
silently changed. -/
noncomputable def encodingEquiv
    [Finite V] [Finite W]
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB) :
    PartPreservingEmbedding A partA B partB ≃
      RelStructure.Embedding
        (withPartsWholeMaskOld A partA)
        (withPartsWholeMaskOld B partB) where
  toFun := encode
  invFun := decode hTransA hTransB
  left_inv := by
    intro e
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.Embedding.ext
    intro x
    rfl

end PartPreservingEmbedding
end StructuralRamsey.PartialSetStructure
