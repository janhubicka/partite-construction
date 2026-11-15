import PartiteConstruction.Functional.TrackBDomainReflectingWholeWeakClosure2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019
import PartiteConstruction.Functional.LocalDomainClosedImage
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019

/-!
# Appendix Track B: local no-phantom condition upgrades one exact EHN weak test

The original-2019 partial homomorphism law preserves entire DEFINED
function value fibres but need not reflect function domains at source-
undefined inputs. As proved in the genuine Fin 2 regression, global
closure-image equality is therefore false even for injective maps.

The necessary extra property can be localized to the exact source
preimage S=f⁻¹(Test) of ONE tested target set. Assume only that a
TARGET-defined input on arguments from S corresponds to a SOURCE-
defined input. On S, this eliminates the phantom-domain obstruction.
Together with original source-defined value equality it implies a
domain-reflecting homomorphism of exact WHOLE-fibre weak restrictions,
and thus generated-closure image equality.

For an ACTUAL finite EHN Stage T use the already verified native
Structure.NoPhantomOn for S=part⁻¹(Test), translated faithfully to
Option(Set): original native empty-valued applications are undefined,
and no artificial defined-empty values are inserted. The true EHN
weak part projection then has exact WHOLE-fibre closure image equality
on this particular saturated tested carrier. Independently verified
complete-mask ambient 2019 UClosureHull source/target dictionaries
give the same literal vertex/seed image equality in the canonical
OLD presentation.

No global ProjectionHom, arbitrary unsaturated S, target H-local
completion, strict functional target B-tree or equality with the
CLIPPED model on arbitrary mixed weak tests is asserted.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- LOCAL independent-domain reflection on exactly S:
every target-defined input tuple coming from S is also source-defined.
No injectivity, finiteness, relation reflection or global-domain
reflection is required. Defined-empty counts as DEFINED. -/
def NoPhantomOn
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) (S : Set V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
    B.Defined F (f ∘ (Subtype.val ∘ xs)) →
      A.Defined F (Subtype.val ∘ xs)

/-- Exact local no-phantom reflection upgrades a source-defined
original-2019 partial map to DOMAIN-REFLECTING on one literal target
whole-weak test and its FULL inverse-image source carrier. -/
theorem IsOriginalPartialHomomorphism.wholeWeakPreimage_domainReflecting_of_noPhantom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (Test : Set W)
    (hNo : NoPhantomOn A B f (f ⁻¹' Test)) :
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
        wholeWeakValue Test (B.func F (f ∘ (Subtype.val ∘ xs)))
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
      exact wholeWeakValue_map_preimage f Test (some U)

/-- For an original-source-defined map, local no-phantom absence on
the exact preimage f⁻¹(Test) suffices for equality of WHOLE weak
closure images, with the original exact weak carriers and seeds.
The arbitrary-S equality is false without full fibre saturation. -/
theorem IsOriginalPartialHomomorphism.wholeWeakPreimage_imageClosure_eq_of_noPhantom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (Test : Set W)
    (hNo : NoPhantomOn A B f (f ⁻¹' Test))
    (Q : Set (f ⁻¹' Test)) :
    Structure.imageSet (restrictMap f Test)
      ((wholeWeakInduce A (f ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce B Test).functionClosure
      (Structure.imageSet (restrictMap f Test) Q) :=
  (hf.wholeWeakPreimage_domainReflecting_of_noPhantom Test hNo)
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

/-- The original EHN projection of a REAL finite Stage has whole-weak
closure image EQUALITY on the exact part-preimage of target Test
provided there are NO native phantom control outputs on tuples in
that source preimage. This condition need NOT hold on all of Stage. -/
theorem Stage.noPhantom_wholeWeakPreimage_imageClosure_eq
    (T : Stage K D)
    (Test : Set P)
    (hNo : T.system.toStructure.NoPhantomOn D T.system.part
      (T.system.part ⁻¹' Test))
    (Q : Set (T.system.part ⁻¹' Test)) :
    Structure.imageSet (restrictMap T.system.part Test)
      ((wholeWeakInduce T.system.toStructure.toNonemptyPartial
        (T.system.part ⁻¹' Test)).functionClosure Q) =
    (wholeWeakInduce D.toNonemptyPartial Test).functionClosure
      (Structure.imageSet (restrictMap T.system.part Test) Q) := by
  let S : Set T.Carrier := T.system.part ⁻¹' Test
  have hf : IsOriginalPartialHomomorphism
      T.system.toStructure.toNonemptyPartial D.toNonemptyPartial T.system.part :=
    T.system.weaklyPartite_toNonemptyPartial_originalHom D T.isPartite
  have hNoPartial :
      PartialSetStructure.NoPhantomOn
        T.system.toStructure.toNonemptyPartial
        D.toNonemptyPartial T.system.part S := by
    intro F xs hTarget
    have hTargetNonempty :
        (D.func F (T.system.part ∘ (Subtype.val ∘ xs))).Nonempty :=
      (Structure.toNonemptyPartial_defined_iff D F _).mp hTarget
    have hSourceNonempty :
        (T.system.toStructure.func F (Subtype.val ∘ xs)).Nonempty :=
      hNo F xs hTargetNonempty
    exact (Structure.toNonemptyPartial_defined_iff
      T.system.toStructure F _).mpr hSourceNonempty
  exact hf.wholeWeakPreimage_imageClosure_eq_of_noPhantom Test hNoPartial Q

/-- The SAME REAL EHN part map, exact weak target Test, full inverse
image source S=part⁻¹(Test), and generator Q satisfy equality in the
canonical induced AMBIENT WHOLE-mask 2019 OLD UClosureHull
presentations, under the explicit local NoPhantomOn hypothesis.

This is not a full global EHN projection or an arbitrary weak
unsaturated S statement. -/
theorem Stage.noPhantom_wholeMaskUClosureHull_image_eq
    (T : Stage K D) (hPos : L.PositiveFuncArity)
    (Test : Set P)
    (hNo : T.system.toStructure.NoPhantomOn D T.system.part
      (T.system.part ⁻¹' Test))
    (Q : Set (T.system.part ⁻¹' Test)) :
    let S := T.system.part ⁻¹' Test
    let g := restrictMap T.system.part Test
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce S) Q) =
    UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (D.toNonemptyPartial.wholeMaskPatternGraph (fun p : P => p))).induce Test)
      (Structure.imageSet g Q) := by
  let S : Set T.Carrier := T.system.part ⁻¹' Test
  let g : S → Test := restrictMap T.system.part Test
  have hSource :
      (wholeWeakInduce T.system.toStructure.toNonemptyPartial S).functionClosure Q =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce S) Q :=
    T.system.toStructure.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      T.system.part hPos T.system.toNonemptyPartial_fibreTransversal S Q
  have hTarget :
      (wholeWeakInduce D.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) =
      UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (D.toNonemptyPartial.wholeMaskPatternGraph (fun p : P => p))).induce Test)
        (Structure.imageSet g Q) :=
    D.toNonemptyPartial.wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
      (fun p : P => p) hPos
      (transversal D).toNonemptyPartial_fibreTransversal Test
      (Structure.imageSet g Q)
  have hEq :
      Structure.imageSet g
        ((wholeWeakInduce T.system.toStructure.toNonemptyPartial S).functionClosure Q) =
      (wholeWeakInduce D.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) :=
    T.noPhantom_wholeWeakPreimage_imageClosure_eq Test hNo Q
  calc
    Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            T.system.part)).induce S) Q) =
        Structure.imageSet g
          ((wholeWeakInduce T.system.toStructure.toNonemptyPartial S).functionClosure Q) :=
      congrArg (Structure.imageSet g) hSource.symm
    _ = (wholeWeakInduce D.toNonemptyPartial Test).functionClosure
        (Structure.imageSet g Q) := hEq
    _ = UClosureHull (L.wholeMaskClosureRules P)
      ((wholeMaskTagExpansion
        (D.toNonemptyPartial.wholeMaskPatternGraph (fun p : P => p))).induce Test)
        (Structure.imageSet g Q) := hTarget

end StructuralRamsey.FunctionalPartite.EHN
