import PartiteConstruction.Functional.TrackCRichDomainEmptyArrow
import PartiteConstruction.Functional.TrackCRichLegalLooseBCover
import PartiteConstruction.Functional.PublishedSparseningLoose

/-!
# Appendix A Track C: ONE genuine rich Option(Set) loose Ramsey/B-cover witness

The first intrinsic local-class endgame needs a *single* finite
candidate with three simultaneous properties:
  1. a full Ramsey arrow in the genuinely partial language;
  2. a selected original-2019 source-defined rich partial
     homomorphism-embedding to the original functional control;
  3. INTERNAL B-copy extension for all exact rich irreducible tests.

A native loose B-cover only yields these conditions after proving the
faithful Dom/Empty extension is legal and transporting BOTH the native
Ramsey arrow and the selected EHN map to the original partial language.

This theorem composes the independently verified full-arrow equivalence
(#708) and the combined legal-loose HE/internal-copy theorem (#714)
with the checked class-free native loose-tree Ramsey construction.
It keeps one actual native witness, one exact decoded carrier, and
one selected q. No collapseDomain, generated closure hull, new
control map, artificial completion target, or positive-arity premise.

This is NOT the full intrinsic locally-finite-subclass Ramsey theorem.
H-relative n-small SAME-target completions and the actual first-stage
class/control bridge remain open.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackECanonicalArrowEquivalence

universe u v
variable {L : Language.{u}} {U V X : Type v}

/-- Given an actual genuine partial Ramsey arrow, construct ONE finite
genuine partial candidate D with the same Ramsey arrow, a selected
source-defined rich HE q into the original control P, and internal
full B copies covering every closed-free-irreducible genuine test.
The decoded output is itself the SAME native loose B-tree after
faithful Dom/Empty re-encoding; its carrier is never altered. -/
theorem sparseningRamsey_richOption_looseFullTrees_BCover
    (A : PartialSetStructure L U)
    (B : PartialSetStructure L V)
    (P : PartialSetStructure L X)
    [Finite U] [Finite V] [Finite X]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : GenuinePartialArrow A B P κ) :
    ∃ (W : Type v) (_ : Finite W) (D : PartialSetStructure L W),
      GenuinePartialArrow A B D κ ∧
      ∃ (q : W → X),
        IsOptionClosedFreeHomomorphismEmbedding D P q ∧
        (∀ {ECarrier : Type v} (E : PartialSetStructure L ECarrier),
          E.IsOptionClosedFreeIrreducible →
          ∀ e : Embedding E D,
            ∃ j : Embedding B D,
              ∀ x : ECarrier, ∃ b : V, e.toFun x = j.toFun b) ∧
        Structure.LooseTreeAmalgam
          B.domainEmptyEncode W D.domainEmptyEncode := by
  classical
  have hNativeArrow :
      Structure.Arrow A.domainEmptyEncode B.domainEmptyEncode
        P.domainEmptyEncode κ :=
    (arrow_iff_canonicalDomainEmpty A B P κ).mpr hArrow
  obtain ⟨W, hFinite, C, hArrowNative, ⟨q, hq⟩,
      hLoose, _hNativeCover, _hLocal⟩ :=
    Structure.sparseningRamsey_functional_looseFullTrees
      A.domainEmptyEncode B.domainEmptyEncode
      P.domainEmptyEncode κ hNativeArrow
  letI : Finite W := hFinite
  let D : PartialSetStructure L W := C.domainEmptyDecode
  have hLegal : Structure.IsLegalDomainEmpty C :=
    hLoose.isLegalDomainEmpty (domainEmptyEncode_isLegal B)
  have hExactDecode : D.domainEmptyEncode = C :=
    hLegal.decodeEncode_eq
  have hRichArrow : GenuinePartialArrow A B D κ := by
    apply (arrow_iff_canonicalDomainEmpty A B D κ).mp
    simpa only [hExactDecode] using hArrowNative
  have hSelectedAndCover :=
    hLoose.richOptionDecoded_HE_and_internalBCover hq
  refine ⟨W, hFinite, D, hRichArrow, q,
    hSelectedAndCover.1, hSelectedAndCover.2, ?_⟩
  simpa only [hExactDecode] using hLoose

end StructuralRamsey.PartialSetStructure
