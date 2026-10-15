import PartiteConstruction.Structure.WeakSubstructure

/-!
# Full functional embeddings commute with exact weak restrictions

This is the most direct functional analogue of the familiar induced
restriction law for relational embeddings. If e:A↪B is a FULL
relation/function embedding and S⊆B is arbitrary, then the restriction
of e to e⁻¹[S] is a full embedding between the two WEAK substructures:

  A|ᵂ(e⁻¹ S)  ↪  B|ᵂS.

No generated function closure of S is needed, and there is no
singleton-valuedness assumption. This is especially useful on both
sides of a genuine full-functional free amalgam: restricting the
original closed root embedding to the exact tested subset still yields
a full root embedding in the weak pieces.

It does NOT say that a globally weak EHN projection has this property;
for that map use the original-partial/singleton-projection interface.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Any full functional embedding restricts to a full embedding from
the exact weak preimage to the exact weak target subset. The inverse
image contains no extra closure vertices. -/
def Embedding.weakRestrictToPreimage
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B) (S : Set V) :
    Embedding (A.weakInduce (e ⁻¹' S)) (B.weakInduce S) where
  toFun := fun x => ⟨e x.1, x.2⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro R x
    change B.rel R (e ∘ (Subtype.val ∘ x)) ↔
      A.rel R (Subtype.val ∘ x)
    exact e.map_rel_iff R (Subtype.val ∘ x)
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hIn : e z.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := by
        rw [← e.map_func F (Subtype.val ∘ x)]
        exact ⟨z.1, hz, rfl⟩
      have hEq : y.1 = e z.1 := (congrArg Subtype.val hzy).symm
      change y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x))
      rw [hEq]
      exact hIn
    · intro hy
      have hyB : y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := hy
      rw [← e.map_func F (Subtype.val ∘ x)] at hyB
      obtain ⟨z, hz, hzy⟩ := hyB
      have hzS : z ∈ e ⁻¹' S := by
        change e z ∈ S
        rw [hzy]
        exact y.2
      refine ⟨(⟨z, hzS⟩ : e ⁻¹' S), hz, ?_⟩
      apply Subtype.ext
      exact hzy

end StructuralRamsey.Structure
