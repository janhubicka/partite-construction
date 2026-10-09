import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Functional.ProjectedWeakImage

/-! # Closed source tests and weak projected images: original partial semantics

In the original 2019 partial-function convention, a homomorphism need
preserve a function fibre only when the input is defined in the source.
An EHN projection of a *closed source test* therefore factors through
the weakly induced structure on the exact image of its vertex set.
The image does not have to be function-closed.

This provides a target-independent composition and pullback interface
for strict full-functional tree targets whose completion maps use the
original partial homomorphism-embedding notion. It is distinct from the
2026 survey's much stronger total-fibre homomorphism requirement.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- Original partial homomorphism-embeddings compose: a defined input
remains defined after the first map, so the second map preserves its
entire function fibre as well. -/
theorem IsOriginalPartialHomomorphismEmbedding.comp
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    {f : U → V} {g : V → W}
    (hg : IsOriginalPartialHomomorphismEmbedding B C g)
    (hf : IsOriginalPartialHomomorphismEmbedding A B f) :
    IsOriginalPartialHomomorphismEmbedding A C (g ∘ f) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R x hx
    exact hg.1.1 R (f ∘ x) (hf.1.1 R x hx)
  · intro F x hdefined
    have hAB := hf.1.2 F x hdefined
    have hBdefined : (B.func F (f ∘ x)).Nonempty := by
      obtain ⟨z, hz⟩ := hdefined
      have himage : f z ∈ imageSet f (A.func F x) := ⟨z, hz, rfl⟩
      rw [hAB] at himage
      exact ⟨f z, himage⟩
    have hBC := hg.1.2 F (f ∘ x) hBdefined
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hab : f a ∈ B.func F (f ∘ x) := by
        rw [← hAB]
        exact ⟨a, ha, rfl⟩
      have hbc : g (f a) ∈ imageSet g (B.func F (f ∘ x)) :=
        ⟨f a, hab, rfl⟩
      rw [hBC] at hbc
      exact hbc
    · intro hz
      have hz' : z ∈ C.func F (g ∘ (f ∘ x)) := by
        simpa only [Function.comp_assoc] using hz
      rw [← hBC] at hz'
      obtain ⟨b, hb, hgb⟩ := hz'
      rw [← hAB] at hb
      obtain ⟨a, ha, hfa⟩ := hb
      exact ⟨a, ha, (congrArg g hfa).trans hgb⟩
  · intro Z E hE e
    obtain ⟨eb, heb⟩ := hf.2 E hE e
    obtain ⟨ec, hec⟩ := hg.2 E hE eb
    exact ⟨ec, fun x => (hec x).trans (congrArg g (heb x))⟩

/-- A full embedding whose range lies in a vertex set remains a full
embedding into the weak induced target on that set. Closure of the
set is NOT required: the embedding's entire output fibres are already
contained in the range of the embedding. -/
def Embedding.codRestrictWeak
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B) (S : Set V)
    (hrange : ∀ a, e a ∈ S) :
    Embedding A (B.weakInduce S) where
  toFun := fun a => ⟨e a, hrange a⟩
  injective := by
    intro a b heq
    apply e.injective
    exact congrArg Subtype.val heq
  map_rel_iff := by
    intro R x
    exact e.map_rel_iff R x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨a, ha, hya⟩
      have himage : e a ∈ imageSet e (A.func F x) := ⟨a, ha, rfl⟩
      rw [e.map_func F x] at himage
      have hval : y.1 = e a := congrArg Subtype.val hya.symm
      change y.1 ∈ B.func F (e ∘ x)
      change y.1 ∈ B.func F (f ∘ x)
      rw [hval]
      exact himage
    · intro hy
      have hval : y.1 ∈ B.func F (e ∘ x) := hy
      rw [← e.map_func F x] at hval
      obtain ⟨a, ha, hea⟩ := hval
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hea

/-- Restrict the *codomain* of a 2019-style partial
homomorphism-embedding to any weak vertex set containing its image.
The set is not required to be closed under target functions. -/
theorem IsOriginalPartialHomomorphismEmbedding.codRestrictWeak
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : IsOriginalPartialHomomorphismEmbedding A B f)
    (S : Set V) (hrange : ∀ a, f a ∈ S) :
    IsOriginalPartialHomomorphismEmbedding A (B.weakInduce S)
      (fun a => (⟨f a, hrange a⟩ : S)) := by
  let fS : U → S := fun a => ⟨f a, hrange a⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R x hx
    exact hf.1.1 R x hx
  · intro F x hdefined
    have hF := hf.1.2 F x hdefined
    ext y
    constructor
    · rintro ⟨a, ha, hya⟩
      have himage : f a ∈ imageSet f (A.func F x) := ⟨a, ha, rfl⟩
      rw [hF] at himage
      have hval : y.1 = f a := congrArg Subtype.val hya.symm
      rw [hval]
      exact himage
    · intro hy
      have hyB : y.1 ∈ B.func F (f ∘ x) := hy
      rw [← hF] at hyB
      obtain ⟨a, ha, hea⟩ := hyB
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hea.symm
  · intro Z E hE e
    obtain ⟨g, hg⟩ := hf.2 E hE e
    have hgrange : ∀ x, g x ∈ S := by
      intro x
      rw [hg x]
      exact hrange (e x)
    exact ⟨g.codRestrictWeak S hgrange,
      fun x => Subtype.ext (hg x)⟩

/-- For a function-closed source test, an EHN projection factors
as an original-2019 partial homomorphism-embedding into the WEAK
induced image on the exact projected vertex set. No target closure
or domain reflection is needed. -/
theorem IsEHNHomomorphismEmbedding.closedToWeakImage_originalPartial
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) (hS : C.IsClosed S) :
    IsOriginalPartialHomomorphismEmbedding
      (C.induce S hS) (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  let inc : Embedding (C.induce S hS) C := inclusion C S hS
  have hsmall : (C.induce S hS).IsEHNHomomorphismEmbedding D
      (p ∘ Subtype.val) :=
    hp.comp inc.isEHNHomomorphismEmbedding
  have hrange : ∀ x : S, (p ∘ Subtype.val) x ∈ p '' S := by
    intro x
    exact ⟨x.1, x.2, rfl⟩
  exact hsmall.toOriginalPartial.codRestrictWeak (p '' S) hrange

/-- Strict full-functional tree targets pull back along original
partial homomorphism-embeddings. Unlike total-fibre pullback, the
map may send an undefined source tuple to a defined target tuple. -/
theorem HasOriginalPartialTreeCompletion.pullback
    {Base : Structure L W} {A : Structure L U} {B : Structure L V}
    (h : HasOriginalPartialTreeCompletion Base B)
    {f : U → V}
    (hf : IsOriginalPartialHomomorphismEmbedding A B f) :
    HasOriginalPartialTreeCompletion Base A := by
  obtain ⟨Y, T, hTree, g, hg⟩ := h
  exact ⟨Y, T, hTree, g ∘ f, hg.comp hf⟩

/-- The complete small-image transfer for the ORIGINAL partial
homomorphism convention. The projected image is weak, not generated
closed, and the strict target is a genuine full B-tree. The only
remaining requirement is a strict completion of that weak image. -/
theorem HasOriginalPartialTreeCompletion.of_closed_EHN_weakImage
    {Base : Structure L W}
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) (hS : C.IsClosed S)
    (hImage :
      HasOriginalPartialTreeCompletion Base (D.weakInduce (p '' S))) :
    HasOriginalPartialTreeCompletion Base (C.induce S hS) :=
  hImage.pullback (hp.closedToWeakImage_originalPartial S hS)

end StructuralRamsey.Structure
