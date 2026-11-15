import PartiteConstruction.Functional.TrackBLocalNoPhantomWholeWeak2019
import PartiteConstruction.Functional.TrackBDomainReflectingClippedWeak2019
import PartiteConstruction.Functional.NativePartiteWeakUClosureRankDictionary
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019

/-!
# Track B: LOCAL no-phantom criterion for the printed clipped weak convention

Track B distinguishes two independent effects of exact weak restriction:
(1) whole-fibre deletion versus clipping partially surviving value fibres,
and (2) source-defined versus domain-reflecting homomorphisms.

An original-2019 source-defined genuine partial map f may create function
domains at source-undefined inputs. The explicit LOCAL NoPhantomOn
condition for the exact full preimage S=f⁻¹(Test) excludes this effect at
exactly the tested inputs, without assuming a globally full map.

The checked weakValue_map_preimage theorem then upgrades the CLIPPED
weak preimage map S→Test to a domain-reflecting homomorphism, even if
f is noninjective. Hence it transports generated closures by EQUALITY.
This gives the CLIPPED counterpart to TrackBLocalNoPhantomWholeWeak2019.

For an actual EHN stage, the already-verified native NoPhantomOn
predicate on its exact part preimage is the required explicit premise.
The independently verified output-part-singleton OLD tagged closure
dictionary converts this to equality of 2019 clipped UClosureHull
images on the literal source and target vertices.

No arbitrary unsaturated weak source test is substituted, no ambient
closure hull is charged to the vertex budget, no globally full EHN
projection is inferred and no H-valued local completion or strict
target B-tree conclusion is asserted.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Local domain reflection on S=f⁻¹(Test) repairs the original 2019
source-defined map under the EXACT CLIPPED weak preimage. Unlike full
global domain reflection, no condition is required outside S. -/
theorem IsOriginalPartialHomomorphism.clippedWeakPreimage_domainReflecting_of_noPhantom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (Test : Set W)
    (hNo : NoPhantomOn A B f (f ⁻¹' Test)) :
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
    cases hA : A.func F (Subtype.val ∘ xs) with
    | none =>
        have hB : B.func F (f ∘ (Subtype.val ∘ xs)) = none := by
          cases hv : B.func F (f ∘ (Subtype.val ∘ xs)) with
          | none => rfl
          | some U =>
              obtain ⟨U', hU'⟩ := hNo F xs ⟨U, hv⟩
              rw [hA] at hU'
              cases hU'
        simp [hA, hB]
    | some U =>
        have hB : B.func F (f ∘ (Subtype.val ∘ xs)) =
            some (Structure.imageSet f U) :=
          hf.2 F (Subtype.val ∘ xs) U hA
        rw [hA, hB]
        exact weakValue_map_preimage f Test (some U)

/-- A source-defined 2019 partial map with no phantom target
domains on ONE full preimage satisfies exact CLIPPED closure-image
equality there, for every seed. Injectivity and closedness of
the tested carrier are not needed. -/
theorem IsOriginalPartialHomomorphism.clippedWeakPreimage_imageClosure_eq_of_noPhantom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (Test : Set W)
    (hNo : NoPhantomOn A B f (f ⁻¹' Test))
    (Q : Set (f ⁻¹' Test)) :
    Structure.imageSet (restrictMap f Test)
      ((weakInduce A (f ⁻¹' Test)).functionClosure Q) =
    (weakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap f Test) Q) :=
  (hf.clippedWeakPreimage_domainReflecting_of_noPhantom Test hNo)
    .image_functionClosure_eq Q

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- For ONE actual EHN Stage and its *original weak* part map,
local native NoPhantomOn on the full preimage of Test suffices for
exact CLIPPED weak generated-closure IMAGE equality. The stored
weak projection alone does not discharge the no-phantom premise. -/
theorem Stage.noPhantom_clippedWeakPreimage_imageClosure_eq
    (T : Stage K D)
    (Test : Set P)
    (hNo : T.system.toStructure.NoPhantomOn D T.system.part
      (T.system.part ⁻¹' Test))
    (Q : Set (T.system.part ⁻¹' Test)) :
    Structure.imageSet (restrictMap T.system.part Test)
      ((weakInduce T.system.toStructure.toNonemptyPartial
        (T.system.part ⁻¹' Test)).functionClosure Q) =
    (weakInduce D.toNonemptyPartial Test).functionClosure
      (Structure.imageSet (restrictMap T.system.part Test) Q) := by
  let S : Set T.Carrier := T.system.part ⁻¹' Test
  have hf : IsOriginalPartialHomomorphism
      T.system.toStructure.toNonemptyPartial D.toNonemptyPartial T.system.part :=
    T.system.weaklyPartite_toNonemptyPartial_originalHom D T.isPartite
  have hNoPartial :
      PartialSetStructure.NoPhantomOn
        T.system.toStructure.toNonemptyPartial D.toNonemptyPartial
        T.system.part S := by
    intro F xs hTarget
    have hTargetNonempty :
        (D.func F (T.system.part ∘ (Subtype.val ∘ xs))).Nonempty :=
      (Structure.toNonemptyPartial_defined_iff D F _).mp hTarget
    have hSourceNonempty :
        (T.system.toStructure.func F (Subtype.val ∘ xs)).Nonempty :=
      hNo F xs hTargetNonempty
    exact (Structure.toNonemptyPartial_defined_iff
      T.system.toStructure F _).mpr hSourceNonempty
  exact hf.clippedWeakPreimage_imageClosure_eq_of_noPhantom Test hNoPartial Q

/-- On ONE exact local no-phantom test, the original finite EHN stage
part map carries the printed CLIPPED source's canonical 2019
output-part-indexed OLD UClosureHull ONTO the same canonical
UClosureHull of the exact control test, for every seed.
These are not the whole-fibre complete-mask tags. -/
theorem Stage.noPhantom_outputTaggedUClosureHull_image_eq
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    (Test : Set P)
    (hNo : T.system.toStructure.NoPhantomOn D T.system.part
      (T.system.part ⁻¹' Test))
    (Q : Set (T.system.part ⁻¹' Test)) :
    let S := T.system.part ⁻¹' Test
    let g := restrictMap T.system.part Test
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q) =
    UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        ((transversal D).splitOutputParts).toStructure.patternGraph).induce Test)
      (Structure.imageSet g Q) := by
  let S : Set T.Carrier := T.system.part ⁻¹' Test
  let g : S → Test := restrictMap T.system.part Test
  let G : Set Test := Structure.imageSet g Q
  have hSource :
      (T.system.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q =
      UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q := by
    calc
      _ = ((T.system.toStructure.weakInduce S).toNonemptyPartial).functionClosure Q := by
        rw [Structure.toNonemptyPartial_weakInduce_commute]
      _ = (T.system.toStructure.weakInduce S).functionClosure Q :=
        (T.system.toStructure.weakInduce S).toNonemptyPartial_functionClosure Q
      _ = _ := T.system.weakFunctionClosure_eq_outputTaggedUClosureHull hPos S Q
  have hTarget :
      (D.toNonemptyPartial.weakInduce Test).functionClosure G =
      UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          ((transversal D).splitOutputParts).toStructure.patternGraph).induce Test) G := by
    calc
      _ = ((D.weakInduce Test).toNonemptyPartial).functionClosure G := by
        rw [Structure.toNonemptyPartial_weakInduce_commute]
      _ = (D.weakInduce Test).functionClosure G :=
        (D.weakInduce Test).toNonemptyPartial_functionClosure G
      _ = _ := (transversal D).weakFunctionClosure_eq_outputTaggedUClosureHull hPos Test G
  have hImage :
      Structure.imageSet g
        ((T.system.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q) =
      (D.toNonemptyPartial.weakInduce Test).functionClosure G :=
    T.noPhantom_clippedWeakPreimage_imageClosure_eq Test hNo Q
  calc
    Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (T.system.splitOutputParts).toStructure.patternGraph).induce S) Q) =
      Structure.imageSet g
        ((T.system.toStructure.toNonemptyPartial.weakInduce S).functionClosure Q) :=
      congrArg (Structure.imageSet g) hSource.symm
    _ = (D.toNonemptyPartial.weakInduce Test).functionClosure G := hImage
    _ = UClosureHull (L.outputPartIndexed P).patternClosureRules
      ((patternTagExpansion
        ((transversal D).splitOutputParts).toStructure.patternGraph).induce Test) G :=
      hTarget

end StructuralRamsey.FunctionalPartite.EHN
