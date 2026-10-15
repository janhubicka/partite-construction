import PartiteConstruction.Functional.WeakSingletonPartialProjection

/-!
# Partial homomorphisms of exact weak singleton-functional substructures

For a genuinely partial SINGLETON-valued function, a weak restriction
may forget an output entirely, making the input undefined. On an input
whose output SURVIVES, the weak fibre equals its original full fibre.
Thus the weak inclusion is an original-2019 source-defined function
homomorphism, though generally NOT a total-fibre homomorphism or a
full functional embedding.

The original-2019 partial function homomorphisms also compose. These
are the direct functional-language operations needed in the
small-image branch of the iterated partite construction. No function
closure is taken on the tested or projected vertex sets.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

/-- Original-2019 source-defined function homomorphisms compose. The
second map is required to preserve its fibre only because the first
map sends a nonempty fibre to another nonempty fibre. -/
theorem IsOriginalPartialHomomorphism.comp
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    {f : U → V} {g : V → W}
    (hg : IsOriginalPartialHomomorphism B C g)
    (hf : IsOriginalPartialHomomorphism A B f) :
    IsOriginalPartialHomomorphism A C (g ∘ f) := by
  constructor
  · intro R x hx
    exact hg.1 R (f ∘ x) (hf.1 R x hx)
  · intro F x hDef
    have hAB := hf.2 F x hDef
    have hBdef : (B.func F (f ∘ x)).Nonempty := by
      obtain ⟨a, ha⟩ := hDef
      have hfval : f a ∈ imageSet f (A.func F x) :=
        ⟨a, ha, rfl⟩
      rw [hAB] at hfval
      exact ⟨f a, hfval⟩
    have hBC := hg.2 F (f ∘ x) hBdef
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hb : f a ∈ B.func F (f ∘ x) := by
        rw [← hAB]
        exact ⟨a, ha, rfl⟩
      have hc : g (f a) ∈ imageSet g (B.func F (f ∘ x)) :=
        ⟨f a, hb, rfl⟩
      rw [hBC] at hc
      simpa only [Function.comp_assoc] using hc
    · intro hz
      have hc : z ∈ C.func F (g ∘ (f ∘ x)) := by
        simpa only [Function.comp_assoc] using hz
      rw [← hBC] at hc
      obtain ⟨b, hb, rfl⟩ := hc
      rw [← hAB] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, ha, rfl⟩

/-- The inclusion of EVERY exact weak substructure of a
singleton-valued partial-function structure is a source-defined
homomorphism. The proof does not require the subset to be closed.
It deliberately does NOT reflect undefined source function inputs. -/
theorem SingletonValued.weakInclusion_originalPartial
    {C : Structure L U} (hC : C.SingletonValued)
    (S : Set U) :
    IsOriginalPartialHomomorphism
      (C.weakInduce S) C Subtype.val := by
  constructor
  · intro R x hx
    exact hx
  · intro F x hDef
    obtain ⟨y, hy⟩ := hDef
    have hyC : y.1 ∈ C.func F (Subtype.val ∘ x) := hy
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      have hzy : z = y.1 :=
        hC F (Subtype.val ∘ x) z y.1 hz hyC
      subst z
      exact ⟨y, hy, rfl⟩


/-- A source-defined partial map with singleton-valued source
continues to preserve its FULL surviving weak fibre even after the
target is restricted to ANY vertex set containing the source image.
It is particularly useful with the exact finite projected weak image,
without requiring target-domain reflection or multivaluedness of the
target. -/
theorem IsOriginalPartialHomomorphism.weakImage_singleton_toSet
    {A : Structure L U} {B : Structure L V} {p : U → V}
    (hp : IsOriginalPartialHomomorphism A B p)
    (hSingle : A.SingletonValued)
    (S : Set U) (I : Set V)
    (hRange : ∀ x : S, p x.1 ∈ I) :
    IsOriginalPartialHomomorphism
      (A.weakInduce S) (B.weakInduce I)
      (fun x : S => (⟨p x.1, hRange x⟩ : I)) := by
  let pS : S → I := fun x => ⟨p x.1, hRange x⟩
  change IsOriginalPartialHomomorphism
    (A.weakInduce S) (B.weakInduce I) pS
  constructor
  · intro R x hx
    change B.rel R (p ∘ (Subtype.val ∘ x))
    exact hp.1 R (Subtype.val ∘ x) hx
  · intro F x hNonempty
    obtain ⟨y₀, hy₀⟩ := hNonempty
    have hDefined : (A.func F (Subtype.val ∘ x)).Nonempty :=
      ⟨y₀.1, hy₀⟩
    have hFull :
        imageSet p (A.func F (Subtype.val ∘ x)) =
          B.func F (p ∘ (Subtype.val ∘ x)) :=
      hp.2 F (Subtype.val ∘ x) hDefined
    ext z
    constructor
    · rintro ⟨y, hy, hEq⟩
      change z.1 ∈ B.func F (p ∘ (Subtype.val ∘ x))
      have hIn : p y.1 ∈ B.func F (p ∘ (Subtype.val ∘ x)) := by
        rw [← hFull]
        exact ⟨y.1, hy, rfl⟩
      have heq : z.1 = p y.1 :=
        (congrArg Subtype.val hEq).symm
      rw [heq]
      exact hIn
    · intro hz
      have hzB : z.1 ∈ B.func F (p ∘ (Subtype.val ∘ x)) := hz
      rw [← hFull] at hzB
      obtain ⟨y, hy, hEq⟩ := hzB
      have hUnique : y = y₀.1 :=
        hSingle F (Subtype.val ∘ x) y y₀.1 hy hy₀
      refine ⟨y₀, hy₀, ?_⟩
      apply Subtype.ext
      change p y₀.1 = z.1
      exact (congrArg p hUnique.symm).trans hEq

end StructuralRamsey.Structure
