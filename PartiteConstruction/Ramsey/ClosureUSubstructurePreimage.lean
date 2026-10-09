import PartiteConstruction.Ramsey.ClosureSemiClosedFreeAmalgam

/-! # Exact inverse images of U-substructures

The original 2019 closure rules are relational.  U-substructure
membership is an exact rooted-tuple closure condition on the specified
vertex set, not a request to generate a larger closed hull.

Preimages of U-substructures under FULL relational embeddings are again
U-substructures.  This is used to show that the two sides of a weak
free-amalgam test are U-closed when the original test is U-closed.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}
variable {rules : ClosureDescription L}

/-- Exact preimage of a U-substructure under an induced embedding. -/
theorem IsUSubstructure.preimage_embedding
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hS : IsUSubstructure rules B S)
    (e : Embedding A B) :
    IsUSubstructure rules A (e ⁻¹' S) := by
  intro rule hrule t ht hRoot j
  have htB : B.rel rule.symbol (e ∘ t) :=
    (e.map_rel_iff rule.symbol t).mpr ht
  exact hS rule hrule (e ∘ t) htB hRoot j

/-- Intersect U-substructures without enlarging either vertex set. -/
theorem IsUSubstructure.inter
    {A : RelStructure L U} {S T : Set U}
    (hS : IsUSubstructure rules A S)
    (hT : IsUSubstructure rules A T) :
    IsUSubstructure rules A (S ∩ T) := by
  intro rule hrule t ht hRoot j
  exact ⟨
    hS rule hrule t ht (fun i => (hRoot i).1) j,
    hT rule hrule t ht (fun i => (hRoot i).2) j⟩

/-- Pull back a U-closed induced test along a full embedding, with
exactly the inverse-image vertices.  The target ambient structure
need not itself be U-closed. -/
theorem IsUClosed.induce_preimage_embedding
    {A : RelStructure L U} {B : RelStructure L V}
    {S : Set V}
    (hA : IsUClosed rules A)
    (hS : IsUSubstructure rules B S)
    (e : Embedding A B) :
    IsUClosed rules (A.induce (e ⁻¹' S)) :=
  hA.induce_of_USubstructure (e ⁻¹' S)
    (hS.preimage_embedding e)

end StructuralRamsey.RelStructure
