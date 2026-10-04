import PartiteConstruction.Structure.IrreducibleHomImage

/-! # Weak homomorphisms for the EHN free-amalgamation theorem

Evans--Hubicka--Nesetril use homomorphisms which preserve relation tuples and
send every function value into a target function value.  Unlike the stronger
`Structure.IsHomomorphism` used elsewhere in this development, no surjectivity
onto the target fibre is required.

Embeddings remain the ordinary full embeddings of `Structure`.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W : Type v}

/-- EHN homomorphism: relations are preserved and function fibres are mapped
into, not necessarily onto, the corresponding target fibres. -/
def IsWeakHomomorphism
    (A : Structure L U) (B : Structure L V) (f : U → V) : Prop :=
  (∀ R x, A.rel R x → B.rel R (f ∘ x)) ∧
  (∀ F x y, y ∈ A.func F x → f y ∈ B.func F (f ∘ x))

namespace IsWeakHomomorphism

variable {A : Structure L U} {B : Structure L V} {C : Structure L W}
variable {f : U → V} {g : V → W}

theorem comp
    (hg : B.IsWeakHomomorphism C g)
    (hf : A.IsWeakHomomorphism B f) :
    A.IsWeakHomomorphism C (g ∘ f) := by
  constructor
  · intro R x hx
    exact hg.1 R (f ∘ x) (hf.1 R x hx)
  · intro F x y hy
    have hfy := hf.2 F x y hy
    have hgy := hg.2 F (f ∘ x) (f y) hfy
    simpa [Function.comp_assoc] using hgy

end IsWeakHomomorphism

namespace Embedding

variable {A : Structure L U} {B : Structure L V}

/-- Every full embedding is, in particular, an EHN weak homomorphism. -/
theorem isWeakHomomorphism (e : Embedding A B) :
    A.IsWeakHomomorphism B e := by
  constructor
  · intro R x hx
    exact (e.map_rel_iff R x).mpr hx
  · intro F x y hy
    have himg : e y ∈ imageSet e (A.func F x) := ⟨y, hy, rfl⟩
    rw [e.map_func F x] at himg
    exact himg

end Embedding

/-- The source-generated weak image.  Its relation/function data consists
exactly of images of source incidences. -/
def weakImage
    (A : Structure L U) (B : Structure L V)
    (f : U → V) : Structure L (Set.range f) where
  rel R x :=
    ∃ y : Fin (L.relArity R) → U,
      A.rel R y ∧ ∀ i, x i = ⟨f (y i), ⟨y i, rfl⟩⟩
  func F x := {z |
    ∃ y : Fin (L.funcArity F) → U, ∃ w : U,
      w ∈ A.func F y ∧
      (∀ i, x i = ⟨f (y i), ⟨y i, rfl⟩⟩) ∧
      z = ⟨f w, ⟨w, rfl⟩⟩}

namespace weakImage

variable {A : Structure L U} {B : Structure L V} {f : U → V}

def quotientMap : U → Set.range f :=
  fun x => ⟨f x, ⟨x, rfl⟩⟩

theorem quotientMap_surjective :
    Function.Surjective (quotientMap (A := A) (B := B) (f := f)) := by
  intro z
  rcases z.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- The quotient onto the source-generated image is a strong homomorphism. -/
theorem quotientMap_hom :
    A.IsHomomorphism (weakImage A B f)
      (quotientMap (A := A) (B := B) (f := f)) := by
  constructor
  · intro R x hx
    exact ⟨x, hx, fun _ => rfl⟩
  · intro F x
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨x, w, hw, fun _ => rfl, rfl⟩
    · rintro ⟨y, w, hw, hxy, hz⟩
      have hyx : y = x := by
        funext i
        have h := congrArg Subtype.val (hxy i)
        exact h
      subst y
      refine ⟨w, hw, ?_⟩
      exact Subtype.ext (congrArg Subtype.val hz)

/-- The inclusion of the generated image into the ambient target is weak. -/
theorem inclusion_weak
    (hf : A.IsWeakHomomorphism B f) :
    (weakImage A B f).IsWeakHomomorphism B Subtype.val := by
  constructor
  · intro R x hx
    rcases hx with ⟨y, hy, hxy⟩
    have hB := hf.1 R y hy
    convert hB using 1
    funext i
    exact congrArg Subtype.val (hxy i)
  · intro F x z hz
    rcases hz with ⟨y, w, hw, hxy, hz⟩
    have hB := hf.2 F y w hw
    change z.1 ∈ B.func F (Subtype.val ∘ x)
    have hargs : Subtype.val ∘ x = f ∘ y := by
      funext i
      exact congrArg Subtype.val (hxy i)
    have hout : z.1 = f w := congrArg Subtype.val hz
    rw [hargs, hout]
    exact hB

end weakImage

/-- Weak homomorphic images of irreducible structures, with the source
incidence structure retained on the image, are irreducible. -/
theorem Irreducible.weakImage
    {A : Structure L U} {B : Structure L V}
    (hA : A.Irreducible) {f : U → V} :
    (weakImage A B f).Irreducible := by
  exact hA.of_surjective_homomorphism
    (weakImage.quotientMap_hom (A := A) (B := B) (f := f))
    (weakImage.quotientMap_surjective (A := A) (B := B) (f := f))

end StructuralRamsey.Structure
