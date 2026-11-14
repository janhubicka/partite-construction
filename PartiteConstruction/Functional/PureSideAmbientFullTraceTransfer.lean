import PartiteConstruction.Functional.AmbientACopyIntersectionsGlue
import PartiteConstruction.Functional.WeakWitnessRestriction

/-!
# Track D: exact pure-copy ambient FULL A-trace transfer

English proof and adversarial gap isolation committed FIRST:
docs/track-d-english-pure-copy-full-A-trace-transfer-20261114.md.

The genuine native functional weak Picture has an irreducible
ambient-A-copy issue on PURE copied-old tests: old target witnesses
protect full OLD A-copies, not automatically all full A-copies of the
larger new attached source whose proper traces meet the old test.

We isolate a precise sufficient SOURCE condition: every genuine full
ambient A-copy of Whole has a genuine FULL old-side lift which agrees
on the LITERAL tested intersection. This condition need not be a
global EHN retraction, full A-label injection or weak-root closure.
Under it, all old target ambient A certificates transport directly.

For a TRUE full functional source free amalgam, irreducibility of A
reduces this condition to cross-side full A-trace lifts, since all
full ambient A-copies lie entirely on one source side.

These statements do NOT construct the hard multi-HJ-line cross-side
trace lifts. That is the exact remaining pure-copy condition for the
weakened no-history native strict functional iteration.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {UA E C Z : Type v}

/-- Transfer TRUE full ambient A-copy target certificates from an old
source side to a larger native full-functional source, when every
ambient full A-copy has an ACTUAL full old-side lift agreeing on the
exact tested vertices.

The existing target map f of the whole weak test is assumed to agree
with the old map on tested old-side positions. The theorem does NOT
construct the target or the ambient-relative weak homomorphism;
those are independent obligations. No closure of the weak test. -/
theorem SetAmbientACopyIntersections.pureSide_of_fullTraceLift
    {A : Structure L UA} {Old : Structure L E}
    {Whole : Structure L C} {Target : Structure L Z}
    (i : Embedding Old Whole)
    (S : Set C) (f : S → Z)
    (fOld : (i ⁻¹' S) → Z)
    (hMap : ∀ x : (i ⁻¹' S),
      f ⟨i x.1, x.2⟩ = fOld x)
    (hOld : SetAmbientACopyIntersections
      A Old Target (i ⁻¹' S) fOld)
    (hTrace : ∀ γ : Embedding A Whole,
      ∃ γOld : Embedding A Old,
        ∀ (a : UA) (ha : γ a ∈ S),
          i (γOld a) = γ a) :
    SetAmbientACopyIntersections A Whole Target S f := by
  intro γ
  obtain ⟨γOld, hAgreement⟩ := hTrace γ
  obtain ⟨γT, hContained, hAgreeOld⟩ := hOld γOld
  refine ⟨γT, hContained, ?_⟩
  intro a ha
  have haOld : γOld a ∈ i ⁻¹' S := by
    change i (γOld a) ∈ S
    rw [hAgreement a ha]
    exact ha
  calc
    γT a = fOld ⟨γOld a, haOld⟩ :=
      hAgreeOld a haOld
    _ = f ⟨i (γOld a), haOld⟩ :=
      (hMap ⟨γOld a, haOld⟩).symm
    _ = f ⟨γ a, ha⟩ := by
      congr 1
      apply Subtype.ext
      exact hAgreement a ha

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}} {UA H E F C Z : Type v}

/-- For a TRUE full native functional source free amalgam, every full
irreducible ambient A-copy lies on one entire SOURCE side.

Consequently, to lift all FULL A-traces of Whole on a given EXACT
vertex set S into the right source side, it is enough to lift
each full LEFT A-copy there on those tested vertices.
No source root or S is assumed function-closed.

In a genuine HJ history the cross-side premise is exactly the
remaining difficult pure-old trace extension, not a consequence of
part-label agreement or pairwise line image intersections. -/
theorem pureRight_fullTraceLift_of_crossSide
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (hCross : ∀ γL : Embedding A Left,
      ∃ γR : Embedding A Right,
        ∀ (a : UA) (ha : iL (γL a) ∈ S),
          iR (γR a) = iL (γL a)) :
    ∀ γ : Embedding A Whole,
      ∃ γR : Embedding A Right,
        ∀ (a : UA) (ha : γ a ∈ S),
          iR (γR a) = γ a := by
  intro γ
  rcases hA hSrc γ with hOnL | hOnR
  · let γL : Embedding A Left :=
      γ.factorThroughClosedRange iL hOnL
    obtain ⟨γR, hAgreement⟩ := hCross γL
    refine ⟨γR, ?_⟩
    intro a ha
    have hFactor : iL (γL a) = γ a :=
      γ.factorThroughClosedRange_spec iL hOnL a
    calc
      iR (γR a) = iL (γL a) := by
        apply hAgreement a
        rw [hFactor]
        exact ha
      _ = γ a := hFactor
  · let γR : Embedding A Right :=
      γ.factorThroughClosedRange iR hOnR
    refine ⟨γR, ?_⟩
    intro a _ha
    exact γ.factorThroughClosedRange_spec iR hOnR a

/-- The complete exact ambient FULL A-copy target certificate on the
whole weak test, obtained by combining the two verified elementary
interfaces: irreducible SOURCE-side localization and faithful
cross-side trace lifting.

This is intentionally NOT the ambient weak HE or full strict B-tree
existence theorem. It is the missing PURE-side A-intersection gate,
conditional on a real FULL old-copy trace, with no history diary. -/
theorem pureRight_ambientACopies_of_crossSideTraces
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C} {Target : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C) (f : S → Z)
    (fR : (iR ⁻¹' S) → Z)
    (hMap : ∀ x : (iR ⁻¹' S),
      f ⟨iR x.1, x.2⟩ = fR x)
    (hCopiesR : SetAmbientACopyIntersections
      A Right Target (iR ⁻¹' S) fR)
    (hCross : ∀ γL : Embedding A Left,
      ∃ γR : Embedding A Right,
        ∀ (a : UA) (ha : iL (γL a) ∈ S),
          iR (γR a) = iL (γL a)) :
    SetAmbientACopyIntersections A Whole Target S f := by
  apply hCopiesR.pureSide_of_fullTraceLift iR S f fR hMap
  exact hSrc.pureRight_fullTraceLift_of_crossSide hA S hCross

end StructuralRamsey.Structure.IsFreeAmalgam
