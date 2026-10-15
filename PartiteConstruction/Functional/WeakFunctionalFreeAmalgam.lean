import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Vertex-exact weak restriction of genuine FULL functional free amalgams

The iterated partite induction must work with weak substructures, not
function-generated closures. This theorem is the direct full-language
analogue of the already-verified relational weak-induced free-amalgam
lemma. All operation fibres are still genuine (possibly multivalued)
sets; a weak subset keeps exactly the outputs inside it.

If C is a FULL free amalgam of Left and Right over Root, then the weak
restriction C|ᵂS to ANY vertex set S is itself the FULL functional free
amalgam of the weak restrictions to the inverse-image side/root sets,
with their canonical full embeddings. No closure hull, assumption of
singleton-valuedness or artificial domain predicates are involved.

The root S∩Root may itself be nonclosed in the ambient C. It is an
honest *weak* substructure, and the exact functional free-amalgam
identities are checked for the weak structures. This is the correct
combinatorial decomposition for the mixed Hales–Jewett Picture step;
it does not by itself supply compatible strict B-tree completions.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- A full functional embedding restricted to any exact source subset
S and target subset T, provided S is the precise preimage of T.
Neither subset is required to be function-closed. -/
def Embedding.weakRestrictExact
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B)
    (S : Set U) (T : Set V)
    (hS : ∀ x, x ∈ S ↔ e x ∈ T) :
    Embedding (A.weakInduce S) (B.weakInduce T) where
  toFun := fun x => ⟨e x.1, (hS x.1).mp x.2⟩
  injective := by
    intro x y heq
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val heq
  map_rel_iff := by
    intro R x
    change B.rel R (e ∘ (Subtype.val ∘ x)) ↔
      A.rel R (Subtype.val ∘ x)
    exact e.map_rel_iff R (Subtype.val ∘ x)
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, heq⟩
      have heF : e z.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := by
        rw [← e.map_func F (Subtype.val ∘ x)]
        exact ⟨z.1, hz, rfl⟩
      have hval : y.1 = e z.1 := (congrArg Subtype.val heq).symm
      change y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x))
      rw [hval]
      exact heF
    · intro hy
      have hyB : y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := hy
      rw [← e.map_func F (Subtype.val ∘ x)] at hyB
      obtain ⟨z, hz, heq⟩ := hyB
      have hzS : z ∈ S := (hS z).mpr (by
        change e z ∈ T
        rw [heq]
        exact y.2)
      refine ⟨(⟨z, hzS⟩ : S), hz, ?_⟩
      apply Subtype.ext
      exact heq

end StructuralRamsey.Structure
