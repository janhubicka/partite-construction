import PartiteConstruction.Structure.RootedFreeAmalgam
import PartiteConstruction.Functional.WeakOperations

set_option autoImplicit false

/-! # Hereditary free-amalgamation classes under the fixed-root reduction -/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R U V : Type v}

/-- A reduced moving structure belongs to the rooted reduction of K when
adjoining the fixed root puts it back in K. -/
def decodedClass (Root : Structure L R)
    (K : Structure.StructureClass.{u,v} (L := L)) :
    Structure.StructureClass.{max u v,v} (L := language L R) :=
  fun C => K (decode Root C)

/-- Heredity and full free amalgamation are transported by decoding. -/
theorem decodedClass_free
    (Root : Structure L R)
    {K : Structure.StructureClass.{u,v} (L := L)}
    (hK : Structure.FreeAmalgamationClass K) :
    Structure.FreeAmalgamationClass (decodedClass Root K) := by
  constructor
  · intro X Y A B hB e
    exact hK.hereditary hB (decodeEmbedding Root e)
  · intro H E F C D A B X sA sB iA iB hA hB hfree
    exact hK.free hA hB (decode_isFreeAmalgam Root hfree)

/-- Inverse full embedding to the canonical split embedding. -/
noncomputable def unsplitEmbedding
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A) :
    Structure.Embedding (decode Root (encode ρ)) A :=
  (Structure.Embedding.id (decode Root (encode ρ))).factorWithMap
    (splitEmbedding ρ) (unsplit ρ)
    (fun x => (split_unsplit ρ x).symm)

@[simp] theorem unsplitEmbedding_apply
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A)
    (x : Sum R (Outside ρ)) :
    unsplitEmbedding ρ x = unsplit ρ x := rfl

/-- Encoding a rooted member of K is a member of the decoded class. -/
theorem encode_mem_decodedClass
    {Root : Structure L R} {A : Structure L U}
    [LT U] (ρ : Structure.Embedding Root A)
    {K : Structure.StructureClass.{u,v} (L := L)}
    (hK : Structure.FreeAmalgamationClass K) (hA : K A) :
    decodedClass Root K (encode ρ) :=
  hK.hereditary hA (unsplitEmbedding ρ)

end StructuralRamsey.Rooted
