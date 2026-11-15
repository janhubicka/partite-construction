import PartiteConstruction.Functional.TrackBDomainReflectingWholeWeakClosure2019
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.EHNStage

/-!
# Track B: clipped exact weak preimages of full-domain partial maps

The printed native functional appendix keeps surviving individual
function values (CLIPPED weak restriction). This is not equal to
WHOLE-fibre deletion on arbitrary multivalued weak tests.

The basic already checked weakValue_map_preimage identity commutes
clipping with exact vertex preimages for EVERY map, including
noninjective maps and the originally defined-empty value.

If the ambient genuine Option(Set) map is DOMAIN-REFLECTING, the
restricted map from exact f⁻¹(Test) to Test is again domain-reflecting
under CLIPPED weak semantics, so it takes images of generated closures
ONTO target generated closures of image seeds, by merged Track B #702.
No injectivity, finite-generation bound or arbitrary ambient closure
hull is needed.

For the old native total-fibre function representation, a FULL
functional homomorphism transports to a genuine domain-reflecting
Option(Set) map by its faithful nonempty-domain decoder. We therefore
supply a conditional actual EHN Stage corollary under the explicit
stronger ProjectionHom assumption. The ordinary stored Stage.isPartite
only provides WeaklyPartiteOver; it is NOT upgraded to ProjectionHom.

This local source-side dictionary is separate from H-valued relative
completion (Track C) and full functional target B-trees (Track D).
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Exact preimages preserve FULL-DOMAIN genuine partial homomorphisms
under the printed CLIPPED weak convention, including repetitions,
nullaries, defined-empty values, and noninjective vertex maps. -/
theorem IsDomainReflectingHomomorphism.clippedWeakRestrictToPreimage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f)
    (Test : Set W) :
    IsDomainReflectingHomomorphism
      (weakInduce A (f ⁻¹' Test))
      (weakInduce B Test)
      (restrictMap f Test) := by
  constructor
  · intro R xs hRel
    change B.rel R (f ∘ (Subtype.val ∘ xs))
    exact hf.1 R (Subtype.val ∘ xs) hRel
  · intro F xs
    change
      (weakValue (f ⁻¹' Test)
        (A.func F (Subtype.val ∘ xs))).map
        (Structure.imageSet (restrictMap f Test)) =
      weakValue Test (B.func F (f ∘ (Subtype.val ∘ xs)))
    rw [← hf.2 F (Subtype.val ∘ xs)]
    exact weakValue_map_preimage f Test
      (A.func F (Subtype.val ∘ xs))

/-- Noninjective full-domain maps carry the generated closure of any
exact CLIPPED weak inverse-image source test onto the target
CLIPPED generated closure of its image seed, with the original
carriers f⁻¹(Test) and Test. This is false for general EHN
source-defined maps or arbitrary unsaturated weak source cuts. -/
theorem IsDomainReflectingHomomorphism.clippedWeakPreimage_imageClosure_eq
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsDomainReflectingHomomorphism A B f)
    (Test : Set W) (Q : Set (f ⁻¹' Test)) :
    Structure.imageSet (restrictMap f Test)
      ((weakInduce A (f ⁻¹' Test)).functionClosure Q) =
    (weakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap f Test) Q) :=
  (hf.clippedWeakRestrictToPreimage Test).image_functionClosure_eq Q

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.Structure

open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- A FULL native set-valued functional homomorphism gives a
domain-reflecting genuine partial map under the faithful convention
where precisely NONEMPTY function values are defined.
No injectivity or relation reflection is needed. -/
theorem IsHomomorphism.toNonemptyPartial_domainReflecting
    {A : Structure L V} {B : Structure L W}
    {f : V → W}
    (hf : A.IsHomomorphism B f) :
    PartialSetStructure.IsDomainReflectingHomomorphism
      A.toNonemptyPartial B.toNonemptyPartial f := by
  classical
  constructor
  · exact hf.1
  · intro F xs
    change
      (if (A.func F xs).Nonempty then some (A.func F xs) else none).map
        (imageSet f) =
      (if (B.func F (f ∘ xs)).Nonempty then
        some (B.func F (f ∘ xs)) else none)
    have hMap : imageSet f (A.func F xs) =
        B.func F (f ∘ xs) := hf.2 F xs
    have hNonempty : (B.func F (f ∘ xs)).Nonempty ↔
        (A.func F xs).Nonempty := by
      rw [← hMap]
      constructor
      · rintro ⟨y, z, hz, _⟩
        exact ⟨z, hz⟩
      · rintro ⟨z, hz⟩
        exact ⟨f z, ⟨z, hz, rfl⟩⟩
    by_cases hA : (A.func F xs).Nonempty
    · have hB : (B.func F (f ∘ xs)).Nonempty :=
        hNonempty.mpr hA
      simp only [hA, hB, if_pos, Option.map_some]
      exact congrArg some hMap
    · have hB : ¬ (B.func F (f ∘ xs)).Nonempty := by
        intro h
        exact hA (hNonempty.mp h)
      simp [hA, hB]

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The full-domain CLIPPED exact-preimage closure equality holds
for an actual native EHN Stage only under the EXPLICIT stronger
hypothesis ProjectionHom. The ordinary stored EHN weak projection
is NOT assumed full. The source weak vertex test is exactly
part⁻¹(Test), not an arbitrary unsaturated S. -/
theorem Stage.fullProjection_clippedWeakPreimage_imageClosure_eq
    (T : Stage K D)
    (hFull : T.system.ProjectionHom D)
    (Test : Set P) (Q : Set (T.system.part ⁻¹' Test)) :
    Structure.imageSet (restrictMap T.system.part Test)
      ((weakInduce T.system.toStructure.toNonemptyPartial
        (T.system.part ⁻¹' Test)).functionClosure Q) =
    (weakInduce D.toNonemptyPartial Test).functionClosure
      (Structure.imageSet (restrictMap T.system.part Test) Q) :=
  (hFull.toNonemptyPartial_domainReflecting).clippedWeakPreimage_imageClosure_eq Test Q

end StructuralRamsey.FunctionalPartite.EHN
