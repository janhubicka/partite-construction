import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Original-2019 partial multivalued projections and singleton output-part masks

A genuine native multivalued operation F has ONE original domain bit:
its fibre is defined when ANY output part is active. Splitting F into
the singleton operations (F,q) creates separate source-definedness
conditions for each q.

Consequently the original-2019 source-defined WHOLE-FIBRE law
implies all the split partial laws. The converse needs a visible
cross-output-part coherence condition: ON AN ORIGINALLY DEFINED
SOURCE FIBRE, every target-required output part must be realized
by a source output. This condition is automatically satisfied by
any native EHN projection (verified source-defined fibre exactness).

This is the exact map-level correction needed before transferring
a singleton-valued U-closed functional iteration back to genuine
multivalued partite systems. It does NOT silently identify
the target-defined/source-undefined phantom case with an empty
set-valued output, nor turn EHN maps globally into full maps.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P : Type v} {V : Type v}

/-- Cross-output-part coherence at ORIGINAL source-defined input
tuples: if a primitive source fibre is nonempty, then EVERY output
part required by the control is realized by an actual source output
of that same part.

No condition is imposed at originally source-undefined inputs,
exactly as in the original-2019 partial homomorphism convention. -/
def System.DefinedOutputPartCoverage
    (B : System L P V) (D : Structure L P) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V),
    (B.func F xs).Nonempty →
    ∀ q : P, q ∈ D.func F (B.part ∘ xs) →
      ∃ y : V, y ∈ B.func F xs ∧ B.part y = q

/-- Even WITHOUT source-defined fibre exactness, weak native
functional incidence preservation transports to every
singleton output-part symbol (F,q). The original part
projection preserves the output-part label by definition.

This is the precise global weak map used in EHN stages:
no function-domain reflection and no target-fibre
surjectivity are claimed for arbitrary source inputs. -/
theorem System.weak_projection_split
    (B : System L P V) (D : Structure L P)
    (h : B.toStructure.IsWeakHomomorphism D B.part) :
    (B.splitOutputParts).toStructure.IsWeakHomomorphism
      ((transversal D).splitOutputParts).toStructure B.part := by
  constructor
  · intro R xs hx
    exact h.1 R.down xs hx
  · intro Fq xs y hy
    exact ⟨h.2 Fq.1.down xs y hy.1, hy.2⟩

/-- A genuine native EHN partite projection therefore has a
GLOBAL weak split-functional part projection. The stronger
full-on-irreducibles EHN map property is not inferred here;
the latter requires independent irreducibility transport. -/
theorem System.weaklyPartite_splitProjectionWeak
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) :
    (B.splitOutputParts).toStructure.IsWeakHomomorphism
      ((transversal D).splitOutputParts).toStructure B.part :=
  B.weak_projection_split D hB.1

/-- Every original-2019 partial homomorphism B→D given by the
ACTUAL part projection induces an original-2019 partial
homomorphism of all singleton output-part operations (F,q).

A nonempty source (F,q) fibre implies the ORIGINAL F source
fibre is defined. The original WHOLE-FIBRE equality restricts
exactly to q on both sides; no global domain reflection. -/
theorem System.originalPartial_projection_split
    (B : System L P V) (D : Structure L P)
    (h : B.toStructure.IsOriginalPartialHomomorphism D B.part) :
    (B.splitOutputParts).toStructure.IsOriginalPartialHomomorphism
      ((transversal D).splitOutputParts).toStructure B.part := by
  constructor
  · intro R xs hx
    exact h.1 R.down xs hx
  · intro Fq xs hnonempty
    rcases Fq with ⟨F, q⟩
    have hDefined : (B.func F.down xs).Nonempty := by
      obtain ⟨y, hy⟩ := hnonempty
      exact ⟨y, hy.1⟩
    have hExact := h.2 F.down xs hDefined
    change imageSet B.part
        {y : V | y ∈ B.func F.down xs ∧ B.part y = q} =
      {p : P | p ∈ D.func F.down (B.part ∘ xs) ∧ p = q}
    ext p
    constructor
    · rintro ⟨y, ⟨hy, hyq⟩, rfl⟩
      refine ⟨?_, hyq⟩
      have him : B.part y ∈ imageSet B.part
          (B.func F.down xs) := ⟨y, hy, rfl⟩
      rw [hExact] at him
      exact him
    · rintro ⟨hp, hpq⟩
      have him : p ∈ imageSet B.part (B.func F.down xs) := by
        rw [hExact]
        exact hp
      obtain ⟨y, hy, hyp⟩ := him
      exact ⟨y, ⟨hy, hyp.trans hpq⟩, hyp⟩

/-- The exact original-multivalued/partial-singleton map
dictionary: original partial WHOLE-FIBRE equality is equivalent
to independent split partial maps PLUS cross-output-part
coverage on every ORIGINAL defined input.

The coverage condition CANNOT be omitted: the split symbol
(F,r) may be source-undefined, even when a different output
part (F,q) is source-defined, while the target has both. -/
theorem System.originalPartial_projection_iff_split_and_coverage
    (B : System L P V) (D : Structure L P) :
    B.toStructure.IsOriginalPartialHomomorphism D B.part ↔
      ((B.splitOutputParts).toStructure.IsOriginalPartialHomomorphism
         ((transversal D).splitOutputParts).toStructure B.part ∧
       B.DefinedOutputPartCoverage D) := by
  constructor
  · intro h
    refine ⟨B.originalPartial_projection_split D h, ?_⟩
    intro F xs hDefined q hq
    have heq := h.2 F xs hDefined
    rw [← heq] at hq
    obtain ⟨y, hy, hyq⟩ := hq
    exact ⟨y, hy, hyq⟩
  · rintro ⟨hSplit, hCover⟩
    constructor
    · intro R xs hx
      exact hSplit.1 (ULift.up R) xs hx
    · intro F xs hDefined
      ext q
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hFqDefined :
            ((B.splitOutputParts).func
              ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), B.part y)
              xs).Nonempty := ⟨y, ⟨hy, rfl⟩⟩
        have him :
            B.part y ∈ imageSet B.part
              ((B.splitOutputParts).func
                ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), B.part y)
                xs) := ⟨y, ⟨hy, rfl⟩, rfl⟩
        rw [hSplit.2
          ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), B.part y)
          xs hFqDefined] at him
        exact him.1
      · intro hq
        obtain ⟨y, hy, hyp⟩ := hCover F xs hDefined q hq
        exact ⟨y, hy, hyp⟩

/-- Native EHN maps automatically have cross-output-part
coverage on every source-defined input: the already checked
EHN fibre-exactness lemma is stronger than this predicate.

This does NOT assert that arbitrary source-undefined inputs
are also target-undefined. -/
theorem System.definedOutputPartCoverage_of_EHN
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) :
    B.DefinedOutputPartCoverage D := by
  intro F xs hDefined q hq
  have hExact := hB.map_func_of_nonempty F xs hDefined
  rw [← hExact] at hq
  obtain ⟨y, hy, hyp⟩ := hq
  exact ⟨y, hy, hyp⟩

end StructuralRamsey.FunctionalPartite
