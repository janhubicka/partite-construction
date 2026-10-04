import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Functional.Attachment

/-! # Binary functional attachment and weak projection invariants

One-copy attachment is an actual full free-amalgam diagram. A finite family
of copies can therefore be attached one at a time, using precisely the class
closure axiom and the same irreducible localization argument at each step.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W X P : Type v}

/-- Weak homomorphism-embeddings glue over a full free amalgam when their
underlying maps agree with the prescribed map on the amalgam. -/
theorem IsWeakHomomorphismEmbedding.of_freeAmalgam
    {Root : Structure L U} {A : Structure L V} {B : Structure L W}
    {C : Structure L X} {D : Structure L P}
    {sA : Embedding Root A} {sB : Embedding Root B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hfree : IsFreeAmalgam sA sB iA iB)
    {qA : V → P} {qB : W → P} {p : X → P}
    (hA : A.IsWeakHomomorphismEmbedding D qA)
    (hB : B.IsWeakHomomorphismEmbedding D qB)
    (hpA : ∀ x, p (iA x) = qA x)
    (hpB : ∀ x, p (iB x) = qB x) :
    C.IsWeakHomomorphismEmbedding D p := by
  constructor
  · constructor
    · intro R z hz
      rcases (hfree.rel_iff R z).mp hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · have ht : p ∘ (iA ∘ x) = qA ∘ x := funext (fun k => hpA (x k))
        rw [ht]
        exact hA.1.1 R x hx
      · have ht : p ∘ (iB ∘ x) = qB ∘ x := funext (fun k => hpB (x k))
        rw [ht]
        exact hB.1.1 R x hx
    · intro F x y hy
      rcases (hfree.func_iff F x y).mp hy with
        ⟨a, b, hb, rfl, rfl⟩ | ⟨a, b, hb, rfl, rfl⟩
      · have ht : p ∘ (iA ∘ a) = qA ∘ a := funext (fun k => hpA (a k))
        rw [ht, hpA b]
        exact hA.1.2 F a b hb
      · have ht : p ∘ (iB ∘ a) = qB ∘ a := funext (fun k => hpB (a k))
        rw [ht, hpB b]
        exact hB.1.2 F a b hb
  · intro Y E hE e
    rcases hE hfree e with hleft | hright
    · choose q hq using hleft
      let eA := e.factorWithMap iA q hq
      obtain ⟨g, hg⟩ := hA.2 E hE eA
      exact ⟨g, fun x => (hg x).trans
        ((hpA (q x)).symm.trans (congrArg p (hq x).symm))⟩
    · choose q hq using hright
      let eB := e.factorWithMap iB q hq
      obtain ⟨g, hg⟩ := hB.2 E hE eB
      exact ⟨g, fun x => (hg x).trans
        ((hpB (q x)).symm.trans (congrArg p (hq x).symm))⟩

namespace Attachment

variable (B : Structure L V) (S : Set V) (hS : B.IsClosed S)
variable (D : Structure L W) (f : Embedding (B.induce S hS) D)

/-- The existing one-copy attachment is the full free amalgam of its core
and attached copy over the closed support. -/
theorem unit_isFreeAmalgam :
    IsFreeAmalgam f (inclusion B S hS)
      (coreEmbedding B S hS D (fun _ : Unit => f))
      (copyEmbedding B S hS D (fun _ : Unit => f) ()) := by
  classical
  let maps := fun _ : Unit => f
  constructor
  · intro z
    cases z with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr b =>
      rcases b with ⟨i, b⟩
      cases i
      exact Or.inr ⟨b.1, (copyMap_not_mem (f := maps) () b.1 b.2).symm⟩
  · intro a b
    constructor
    · intro hab
      have hb : b ∈ S := mem_of_copyMap_eq_inl hab.symm
      refine ⟨⟨b, hb⟩, ?_, rfl⟩
      have h := hab
      change Sum.inl a = copyMap B S hS D maps () b at h
      rw [copyMap_mem () b hb] at h
      exact Sum.inl.inj h
    · rintro ⟨b, rfl, rfl⟩
      exact (copy_extends B S hS D maps () b).symm
  · intro R z
    constructor
    · rintro (⟨x, hx, heq⟩ | ⟨i, x, hx, heq⟩)
      · exact Or.inl ⟨x, hx, heq⟩
      · cases i
        exact Or.inr ⟨x, hx, heq⟩
    · rintro (⟨x, hx, heq⟩ | ⟨x, hx, heq⟩)
      · exact Or.inl ⟨x, hx, heq⟩
      · exact Or.inr ⟨(), x, hx, heq⟩
  · intro F x y
    constructor
    · rintro (⟨a, b, hb, hx, hy⟩ | ⟨i, a, b, hb, hx, hy⟩)
      · exact Or.inl ⟨a, b, hb, hx, hy⟩
      · cases i
        exact Or.inr ⟨a, b, hb, hx, hy⟩
    · rintro (⟨a, b, hb, hx, hy⟩ | ⟨a, b, hb, hx, hy⟩)
      · exact Or.inl ⟨a, b, hb, hx, hy⟩
      · exact Or.inr ⟨(), a, b, hb, hx, hy⟩

end Attachment
end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.Attachment

open Structure

universe u v
variable {L : Language.{u}} {P V W : Type v}
variable (B : System L P V) (S : Set V) (hS : B.toStructure.IsClosed S)
variable (E : System L P W) (f : FunctionalPartite.Embedding (B.induce S hS) E)

theorem unit_weaklyPartiteOver
    (D : Structure L P) (hB : B.WeaklyPartiteOver D)
    (hE : E.WeaklyPartiteOver D) :
    (attach B S hS E (fun _ : Unit => f)).WeaklyPartiteOver D := by
  apply Structure.IsWeakHomomorphismEmbedding.of_freeAmalgam
    (Structure.Attachment.unit_isFreeAmalgam B.toStructure S hS E.toStructure f.toEmbedding)
    hE hB
  · intro x
    rfl
  · intro x
    exact part_copyMap B S hS E (fun _ : Unit => f) () x

theorem unit_mem
    {K : Structure.StructureClass (L := L)} (hK : Structure.FreeAmalgamationClass K)
    (hB : K B.toStructure) (hE : K E.toStructure) :
    K (attach B S hS E (fun _ : Unit => f)).toStructure :=
  hK.free hE hB
    (Structure.Attachment.unit_isFreeAmalgam B.toStructure S hS E.toStructure f.toEmbedding)

end StructuralRamsey.FunctionalPartite.Attachment
