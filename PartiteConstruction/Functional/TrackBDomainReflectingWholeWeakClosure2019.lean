import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track B: exact whole-weak closure image for full-domain partial maps

An original-2019 source-defined partial homomorphism need not reflect
undefined function inputs, hence generally gives only inclusion of
generated closure images (verified sharp Fin 2 regression #682).

The stronger IsDomainReflectingHomomorphism preserves ALL Option(Set)
values and definedness, but does not require vertex injectivity or
reflection of relations. It preserves function-closed image subsets,
hence exact equality of generated-closure images, even when vertices
are identified. The exact wholeWeakValue_map_preimage equation lifts
this to ANY literal target test and its exact full source preimage.

This does not upgrade arbitrary EHN weak projections to full maps,
does not work on arbitrary non-fibre-saturated source cuts, and
does not construct H-relative local or strict B-tree completions.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Full-domain genuine partial maps carry closed source sets to
closed target images, without vertex injectivity or relation
reflection. This includes nullaries and defined-empty fibres. -/
theorem IsDomainReflectingHomomorphism.image_isClosed
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f)
    (S : Set V) (hS : A.IsClosed S) :
    B.IsClosed (Structure.imageSet f S) := by
  classical
  intro F ys T hys hValue y hy
  have hLifts : ∀ i : Fin (L.funcArity F),
      ∃ x : V, x ∈ S ∧ f x = ys i := hys
  choose xs hxs hfx using hLifts
  have hTuple : f ∘ xs = ys := by
    funext i
    exact hfx i
  have hMap :
      (A.func F xs).map (Structure.imageSet f) = some T := by
    rw [hf.2 F xs, hTuple, hValue]
  cases hA : A.func F xs with
  | none =>
      simp [hA] at hMap
  | some U =>
      have hImage : Structure.imageSet f U = T := by
        simpa [hA] using hMap
      have hPre : y ∈ Structure.imageSet f U := by
        rw [hImage]
        exact hy
      obtain ⟨z, hz, hfz⟩ := hPre
      exact ⟨z, hS F xs U hxs hA hz, hfz⟩

/-- Full-domain reflection, not injectivity, makes the image of
generated closure equal target generated closure of the image seed. -/
theorem IsDomainReflectingHomomorphism.image_functionClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f)
    (Q : Set V) :
    Structure.imageSet f (A.functionClosure Q) =
    B.functionClosure (Structure.imageSet f Q) := by
  apply Set.Subset.antisymm
  · exact hf.toOriginalPartial.image_functionClosure_subset Q
  · have hClosed : B.IsClosed
        (Structure.imageSet f (A.functionClosure Q)) :=
      hf.image_isClosed _ (A.functionClosure_isClosed Q)
    apply B.functionClosure_least hClosed
    rintro y ⟨x, hx, hxy⟩
    exact ⟨x, A.subset_functionClosure Q hx, hxy⟩

/-- A full-domain map restricts to its EXACT whole-fibre weak
preimage without injectivity, added vertices or new domain masks. -/
theorem IsDomainReflectingHomomorphism.wholeWeakRestrictToPreimage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f) (Test : Set W) :
    IsDomainReflectingHomomorphism
      (wholeWeakInduce A (f ⁻¹' Test))
      (wholeWeakInduce B Test)
      (restrictMap f Test) := by
  constructor
  · intro R xs hRel
    change B.rel R (f ∘ (Subtype.val ∘ xs))
    exact hf.1 R (Subtype.val ∘ xs) hRel
  · intro F xs
    change
      (wholeWeakValue (f ⁻¹' Test)
        (A.func F (Subtype.val ∘ xs))).map
        (Structure.imageSet (restrictMap f Test)) =
      wholeWeakValue Test
        (B.func F (f ∘ (Subtype.val ∘ xs)))
    rw [← hf.2 F (Subtype.val ∘ xs)]
    exact wholeWeakValue_map_preimage f Test
      (A.func F (Subtype.val ∘ xs))

/-- Exact whole-fibre weak closure IMAGE equality under a genuinely
full-domain (possibly noninjective) partial homomorphism, on
literal preimage f⁻¹(Test) and Test, every seed Q. -/
theorem IsDomainReflectingHomomorphism.wholeWeakPreimage_imageClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f)
    (Test : Set W) (Q : Set (f ⁻¹' Test)) :
    Structure.imageSet (restrictMap f Test)
      ((wholeWeakInduce A (f ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap f Test) Q) :=
  (hf.wholeWeakRestrictToPreimage Test).image_functionClosure_eq Q

end StructuralRamsey.PartialSetStructure
