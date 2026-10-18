import PartiteConstruction.Structure.Basic

/-!
# Full functional homomorphisms send function-closed sets to closed sets

If f maps the ENTIRE function output set onto the target output
set on EVERY input, then the actual image of any closed source
set is function-closed in the target. No injectivity or
surjectivity onto the whole target is required.

This result is FALSE for a merely EHN/original-2019 partial
projection at a source-undefined input, since the target can
have extra outputs there. The verified unary EHN-to-full theorem
is what makes this lemma applicable to closed unary Picture
side tests in the native iterated construction.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Whole-fibre equality forces the image of a genuinely
function-closed source vertex subset to be closed in the
functional target. Does NOT apply to a general weak EHN map. -/
theorem IsHomomorphism.image_isClosed
    {C : Structure L U} {D : Structure L V}
    {f : U → V}
    (hf : C.IsHomomorphism D f)
    (S : Set U) (hS : C.IsClosed S) :
    D.IsClosed (f '' S) := by
  classical
  intro F ys hys z hz
  have hLifts :
      ∀ i : Fin (L.funcArity F),
        ∃ x : U, x ∈ S ∧ f x = ys i := hys
  choose xs hxs using hLifts
  have hArgs : f ∘ xs = ys := by
    funext i
    exact (hxs i).2
  have hOutput : z ∈ D.func F (f ∘ xs) := by
    rwa [hArgs]
  have hImage : z ∈ imageSet f (C.func F xs) := by
    rw [hf.2 F xs]
    exact hOutput
  obtain ⟨x, hx, hxEq⟩ := hImage
  exact ⟨x, hS F xs (fun i => (hxs i).1) hx, hxEq⟩

end StructuralRamsey.Structure
