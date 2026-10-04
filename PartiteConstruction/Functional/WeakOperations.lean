import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Functional.Operations

/-! # Closed restrictions of weak partite systems

Full embeddings can be cancelled on the target side. This packages the
restriction and factorization arguments without identifying weak maps with
full homomorphisms.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

/-- Cancel a full target embedding while keeping a specified underlying map. -/
def Embedding.factorWithMap
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    (e : Embedding A C) (j : Embedding B C) (f : U → V)
    (h : ∀ x, e x = j (f x)) : Embedding A B where
  toFun := f
  injective := by
    intro x y hxy
    apply e.injective
    rw [h x, h y, hxy]
  map_rel_iff := by
    intro R x
    have ht : e ∘ x = j ∘ (f ∘ x) := funext (fun k => h (x k))
    rw [← j.map_rel_iff R (f ∘ x), ← ht, e.map_rel_iff]
  map_func := by
    intro F x
    have ht : e ∘ x = j ∘ (f ∘ x) := funext (fun k => h (x k))
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have he : e z ∈ C.func F (e ∘ x) := by
        rw [← e.map_func F x]
        exact ⟨z, hz, rfl⟩
      rw [ht, h z, ← j.map_func F (f ∘ x)] at he
      obtain ⟨b, hb, heq⟩ := he
      exact j.injective heq ▸ hb
    · intro hy
      have hj : j y ∈ C.func F (e ∘ x) := by
        rw [ht, ← j.map_func F (f ∘ x)]
        exact ⟨y, hy, rfl⟩
      rw [← e.map_func F x] at hj
      obtain ⟨z, hz, heq⟩ := hj
      exact ⟨z, hz, j.injective ((h z).symm.trans heq)⟩

noncomputable def Embedding.factorThroughClosedRange
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    (e : Embedding A C) (j : Embedding B C)
    (h : ∀ x, ∃ y, e x = j y) : Embedding A B :=
  e.factorWithMap j (fun x => Classical.choose (h x))
    (fun x => Classical.choose_spec (h x))

/-- Weak maps can also be cancelled through a full target embedding. -/
theorem Embedding.cancel_weak
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    (j : Embedding B C) {f : U → V}
    (hf : A.IsWeakHomomorphism C (j ∘ f)) :
    A.IsWeakHomomorphism B f := by
  constructor
  · intro R x hx
    exact (j.map_rel_iff R (f ∘ x)).mp (hf.1 R x hx)
  · intro F x y hy
    have h := hf.2 F x y hy
    rw [← j.map_func F (f ∘ x)] at h
    obtain ⟨b, hb, heq⟩ := h
    exact j.injective heq ▸ hb

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}

namespace System

variable (B : System L P V) (D : Structure L P)
variable (hB : B.toStructure.IsWeakHomomorphism D B.part)
variable (A : Structure L U) (α : Structure.Embedding A D)

theorem weak_support_closed :
    B.toStructure.IsClosed (B.support α.toFunctionEmbedding) :=
  hB.preimage_isClosed (Set.range α) α.range_isClosed

noncomputable def weakRestrict :
    System L U (B.support α.toFunctionEmbedding) where
  toStructure := B.toStructure.induce _ (weak_support_closed B D hB A α)
  part := B.restrictedPart α.toFunctionEmbedding
  relTransversal R x hx i j hp := by
    apply Subtype.ext
    apply B.relTransversal R (Subtype.val ∘ x) hx i j
    exact (B.restrictedPart_spec α.toFunctionEmbedding (x i)).symm.trans
      ((congrArg α hp).trans (B.restrictedPart_spec α.toFunctionEmbedding (x j)))
  funcTransversal F x y z hy hz hp := by
    apply Subtype.ext
    apply B.funcTransversal F (Subtype.val ∘ x) y.1 z.1 hy hz
    exact (B.restrictedPart_spec α.toFunctionEmbedding y).symm.trans
      ((congrArg α hp).trans (B.restrictedPart_spec α.toFunctionEmbedding z))

noncomputable def weakRestrictInclusion :
    Structure.Embedding (weakRestrict B D hB A α).toStructure B.toStructure :=
  Structure.inclusion _ _ (weak_support_closed B D hB A α)

theorem weakRestrict_projection :
    (weakRestrict B D hB A α).toStructure.IsWeakHomomorphism A
      (weakRestrict B D hB A α).part := by
  apply α.cancel_weak
  have hmap : α ∘ (weakRestrict B D hB A α).part = B.part ∘ Subtype.val :=
    funext (fun x => B.restrictedPart_spec α.toFunctionEmbedding x)
  rw [hmap]
  exact hB.comp (weakRestrictInclusion B D hB A α).isWeakHomomorphism

theorem weakRestrict_invariant (hI : B.WeaklyPartiteOver D) :
    (weakRestrict B D hB A α).WeaklyPartiteOver A := by
  refine ⟨weakRestrict_projection B D hB A α, ?_⟩
  intro X E hE e
  let inc := weakRestrictInclusion B D hB A α
  obtain ⟨g, hg⟩ := hI.2 E hE (inc.comp e)
  let q : X → U := fun x => (weakRestrict B D hB A α).part (e x)
  have hfac : ∀ x, g x = α (q x) := by
    intro x
    exact (hg x).trans (B.restrictedPart_spec α.toFunctionEmbedding (e x)).symm
  exact ⟨g.factorWithMap α q hfac, fun _ => rfl⟩

end System

/-- Restrict a full A-copy with the prescribed part map to the closed support. -/
noncomputable def weakRestrictCopy
    (B : System L P V) (D : Structure L P)
    (hB : B.toStructure.IsWeakHomomorphism D B.part)
    (A : Structure L U) (α : Structure.Embedding A D)
    (e : Structure.Embedding A B.toStructure)
    (he : ∀ x, B.part (e x) = α x) :
    FunctionalPartite.Embedding (transversal A) (B.weakRestrict D hB A α) := by
  let q : U → B.support α.toFunctionEmbedding :=
    fun x => ⟨e x, x, (he x).symm⟩
  refine {
    toEmbedding := e.factorWithMap (B.weakRestrictInclusion D hB A α) q (fun _ => rfl)
    map_part := ?_
  }
  intro x
  apply α.injective
  exact (B.restrictedPart_spec α.toFunctionEmbedding (q x)).trans (he x)

end StructuralRamsey.FunctionalPartite
