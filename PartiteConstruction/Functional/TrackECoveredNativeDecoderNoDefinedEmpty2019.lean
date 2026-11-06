import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.TrackECanonicalArrowEquivalence

/-!
# Appendix A Track E: protected B coverage forces native decoder normality

The final 2019 two-pass profiled Picture is relational until the
complete OLD value/domain relations are decoded into genuine
`Option (Set)` partial functions.

We prove the missing normality theorem WITHOUT adding a normality
oracle: if the canonical base has no defined-empty values and the
FINAL tagged Picture has the already checked U-closed / U-irreducible
protected B-copy coverage, then every decoded defined operation has
a genuinely nonempty output.

The argument is sharper than positive-arity decoder coherence:
the support of one actual complete OLD value tuple is ordinarily
irreducible, so the EXISTING covered-weak-irreduci​ble test lemma
embeds that exact tuple support into the canonical B. Its FULL
embedding reflects the complete value set; a chosen output vertex
in B certifies an output position in the same original tuple.

No generator hull is substituted for the exact test, no relational
Picture is assumed canonical, and no full global EHN projection
or strict mixed-root functional tree is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Every actual COMPLETE OLD output set in a U-closed protected
B-covered tagged target must be nonempty whenever the canonical
genuine-partial Base has no defined-empty functions.

Unlike the complete decoder coherence theorem, this implication does
not require positive primitive function arity or value uniqueness:
it works directly on one literal complete OLD tuple, including
nullaries, repeated inputs, and multivalued outputs. -/
theorem wholeMaskValue_nonempty_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (hBase : NoDefinedEmptyValues Base)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U : Set V)
    (hValue : HasWholeMaskValue (wholeMaskTagReduct C) F x U) :
    U.Nonempty := by
  classical
  obtain ⟨m, r, hr, q, t, hGraph, _hArgs, hOutputs⟩ := hValue
  let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  let S : Set V := Set.range t
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inr (pat, q)))) t hGraph
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hClosed hCover S hIrred
  let tS : Fin (m + q.size) → S :=
    fun i => ⟨t i, ⟨i, rfl⟩⟩
  have hB : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (pat, q))) (g ∘ tS) :=
    (g.map_rel_iff (.inl (.inr (.inr (pat, q)))) tS).mpr hGraph
  have hValueB :
      Base.func F
        ((fun i : Fin m => (g ∘ tS) (Fin.castAdd q.size i)) ∘ r) =
      some (Set.range (fun j : Fin q.size =>
        (g ∘ tS) (Fin.natAdd m j))) := hB.2.1
  obtain ⟨y, ⟨j, _hj⟩⟩ :=
    hBase F
      ((fun i : Fin m => (g ∘ tS) (Fin.castAdd q.size i)) ∘ r)
      (Set.range (fun j : Fin q.size =>
        (g ∘ tS) (Fin.natAdd m j))) hValueB
  refine ⟨t (Fin.natAdd m j), ?_⟩
  rw [hOutputs]
  exact ⟨j, rfl⟩

/-- The GENERIC genuine-partial decoder of the final tagged old
reduct has no defined-empty values. This conclusion is forced by the
SAME protected coverage hypothesis and normality of its Base;
the decoder is not assumed to be canonical beforehand.

No positive-arity, coherence, finite-carrier, or value-uniqueness
hypothesis is needed: `wholeMaskPartialDecode` chooses an actual
complete OLD value witness whenever it returns `some U`. -/
theorem wholeMaskPartialDecode_noDefinedEmpty_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (hBase : NoDefinedEmptyValues Base) :
    NoDefinedEmptyValues
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) := by
  classical
  intro F x U hSome
  let E := wholeMaskTagReduct C
  by_cases hExists : ∃ T : Set V, HasWholeMaskValue E F x T
  · have hChosen : HasWholeMaskValue E F x (Classical.choose hExists) :=
      Classical.choose_spec hExists
    have hEq : Classical.choose hExists = U := by
      simpa [wholeMaskPartialDecode, hExists] using hSome
    rw [← hEq]
    exact wholeMaskValue_nonempty_of_closed_coverage
      C Base part hClosed hCover hBase F x _ hChosen
  · have hFalse : False := by
      simpa [wholeMaskPartialDecode, hExists] using hSome
    exact hFalse.elim

end StructuralRamsey.RelStructure

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Naming unary part predicates does not create defined-empty
operations, since the entire original Option(Set) value is unchanged. -/
theorem NoDefinedEmptyValues.withParts
    (Base : PartialSetStructure L W) (part : W → P)
    (hBase : NoDefinedEmptyValues Base) :
    NoDefinedEmptyValues (Base.withParts part) := by
  intro F x S hValue
  exact hBase F.down x S hValue

/-- The ACTUAL final 2019 part-labelled OLD decoder inherits the
no-defined-empty property from canonical B, under exactly the
already proved final U-closed/protected B-cover premises. -/
theorem wholeMaskOriginalDecode_noDefinedEmpty_of_closed_coverage
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hBase : NoDefinedEmptyValues Base) :
    NoDefinedEmptyValues (wholeMaskOriginalDecode C) := by
  have hAll : NoDefinedEmptyValues
      ((wholeMaskTagReduct C).wholeMaskPartialDecode) :=
    wholeMaskPartialDecode_noDefinedEmpty_of_closed_coverage
      C (Base.withParts basePart) basePart hClosed hCover
      (hBase.withParts basePart)
  intro F x S hValue
  exact hAll (ULift.up F) x S hValue

/-- Direct native-B specialization: no extra decoder-normality oracle.
The base is exactly B.toNonemptyPartial in the genuine partial syntax,
so it has no defined-empty inputs by the merged Track E equivalence. -/
theorem wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (B : Structure L W) (basePart : W → P)
    (hClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          (((B.toNonemptyPartial).withParts basePart).wholeMaskPatternGraph basePart)))) :
    NoDefinedEmptyValues (wholeMaskOriginalDecode C) := by
  exact wholeMaskOriginalDecode_noDefinedEmpty_of_closed_coverage
    C B.toNonemptyPartial basePart hClosed hCover
    (toNonemptyPartial_noDefinedEmpty B)

/-- The normality-gated native Ramsey decoder from merged Track E
PR #562 is now UNCONDITIONAL ONCE THE REAL 2019 COVERAGE PREMISES
AND A NATIVE B ARE SUPPLIED. Same A, B, actual final decoded C
and every full A/B embedding; no witness or vertex carrier is changed.

This transports Ramsey arrows across the final functional decoder,
but does not by itself construct a 2019 covered C or assert that
strict functional tree-amalgam locality follows from the OLD encoding. -/
theorem nativeArrow_iff_coveredPartialArrow
    (A : Structure L W) (B : Structure L W)
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (basePart : W → P)
    (hClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          (((B.toNonemptyPartial).withParts basePart).wholeMaskPatternGraph basePart))))
    (κ : Type*) :
    Structure.Arrow A B (wholeMaskOriginalDecode C).collapseDomain κ ↔
    StructuralRamsey.Structure.TrackECanonicalArrowEquivalence.GenuinePartialArrow
      A.toNonemptyPartial B.toNonemptyPartial (wholeMaskOriginalDecode C) κ := by
  exact StructuralRamsey.Structure.TrackECanonicalArrowEquivalence.arrow_iff_partialTarget_of_noDefinedEmpty
    A B (wholeMaskOriginalDecode C) κ
    (wholeMaskOriginalDecode_noDefinedEmpty_of_nativeBCover
      C B basePart hClosed hCover)

end StructuralRamsey.PartialSetStructure
