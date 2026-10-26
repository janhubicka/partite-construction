import PartiteConstruction.Functional.WholeMaskCanonicalEmbeddingInverse2019
import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019
import PartiteConstruction.Ramsey.ClosurePartPredicates

/-!
# Unary part predicates make the full genuine-function encoding faithful

The OLD complete-mask graph has output-part labels, but they need not
name the parts of vertices that never occur in any function output.
The previously verified relational `withPartPredicates` expansion
adds exactly one unary part predicate per vertex on the SAME carrier.

Hence FULL part-preserving Option(Set) functional embeddings are
represented by FULL OLD complete-mask relational embeddings with
unary part predicates, and conversely FULL such relational embeddings
decode to genuine full partial-function embeddings that preserve the
chosen part map.

This is the part-preserving embedding interface needed to transport
the unrestricted 2019 partite-Picture Ramsey arrow. It uses the
existing unary-part-predicate library, not a new incompatible
part-labelling convention. No nonclosed weak test is completed by
adding vertices, and none is never identified with some empty.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- Genuinely partial FULL embeddings equipped with a full
vertex-by-vertex part-preservation certificate. -/
def PartPreservingEmbedding
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (partA : V → P) (partB : W → P) : Type _ :=
  {e : Embedding A B // ∀ x : V,
    partB (e.toFun x) = partA x}

/-- The unary part-predicate expansion of the OLD COMPLETE
function-domain and full-value relational encoding. -/
def wholeMaskPartLabelledGraph
    (A : PartialSetStructure L V) (part : V → P) :=
  (A.wholeMaskPatternGraph part).expandPartPredicates part

/-- Encode every full role-preserving genuinely partial function
embedding as a FULL induced relational embedding, including the
unary predicates that name the parts of isolated vertices. -/
noncomputable def PartPreservingEmbedding.toWholeMaskPartLabelled
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {partA : V → P} {partB : W → P}
    (e : PartPreservingEmbedding A B partA partB) :
    RelStructure.Embedding
      (wholeMaskPartLabelledGraph A partA)
      (wholeMaskPartLabelledGraph B partB) :=
  (e.1.wholeMaskPatternGraph partA partB e.2).expandPartPredicates
    partA partB e.2

/-- Conversely, an induced embedding of the unary part-labelled
COMPLETE OLD graphs gives a FULL genuine Option(Set) embedding
together with correct part preservation, on the original carrier.
This uses the checked source decoder equality and domain reflection;
it does not reconstruct a weak EHN projection. -/
noncomputable def PartPreservingEmbedding.ofWholeMaskPartLabelled
    (A : PartialSetStructure L V) [Finite V]
    (B : PartialSetStructure L W) [Finite W]
    (partA : V → P) (partB : W → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (e : RelStructure.Embedding
      (wholeMaskPartLabelledGraph A partA)
      (wholeMaskPartLabelledGraph B partB)) :
    PartPreservingEmbedding A B partA partB := by
  let f : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) :=
    e.forgetPartPredicates
  let g : Embedding A B :=
    Embedding.ofCanonicalWholeMaskPatternGraph
      A B partA partB hTransA hTransB f
  refine ⟨g, ?_⟩
  intro x
  change partB (e.toFun x) = partA x
  exact e.expanded_preserves_part x

end StructuralRamsey.PartialSetStructure
