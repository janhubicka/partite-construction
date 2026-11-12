import PartiteConstruction.Functional.TrackEFinalCoveredDecodedClosedU2019
import PartiteConstruction.Functional.WholeMaskTargetOutputHull2019

/-!
# Track E: full closedness dictionary for the ACTUAL final covered tagged witness

The original 2019 two-pass final C is U-closed, B-covered and need not
syntactically equal the canonical tag expansion of its decoded functional
structure. This module proves the SAME-CARRIER relative closure predicate
is nevertheless equivalent to ordinary closure under its actual decoded
Option(Set) functions (under the existing positive-arity and B-coverage
assumptions).

The new direction uses the verified positive complete-value OLD tuple
to U-closure-hull theorem, not a replacement of the TESTED vertex set
by its hull: this hull is solely an intermediate witness that a relative
U-substructure contains every decoded output of inputs it contains.
The other direction is the independent #621 exact closedness lemma.

This completes the closure-transport side of the remaining Track E
exact native irreducible-test problem. It is NOT itself a proof of
U-irreducibility or of the full native global homomorphism-embedding.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- A relative U-substructure of the final covered tagged C is precisely
closed under its actual decoded genuine partial functions, on the SAME S.
The proof uses the old complete output tuple whose entire range is the
decoded value, then the verified target-side input-hull localization. -/
theorem wholeMaskCovered_USubstructure_to_decodedClosed
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hUSub : IsUSubstructure (L.wholeMaskClosureRules P) C S) :
    ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S := by
  classical
  let E : RelStructure (L.wholeMaskPatternLanguage P) V :=
    wholeMaskTagReduct C
  have hNormal : WholeMaskTagNormal C :=
    wholeMaskTagNormal_of_closed_coverage C Base part hC hCover
  have hValid : HasValidCompleteMaskDomains E :=
    wholeMask_validCompleteDomains_of_closed_coverage C Base part hC hCover
  intro F xs U hXs hValue
  have hUnique (T T' : Set V)
      (hT : HasWholeMaskValue E F xs T)
      (hT' : HasWholeMaskValue E F xs T') : T = T' :=
    wholeMaskValue_unique_of_closed_coverage
      C Base part hC hPos hCover F xs T T' hT hT'
  obtain ⟨m, r, hr, q, t, hGraph, hArgs, hOutput⟩ :=
    (E.wholeMaskPartialDecode_func_some_iff
      F xs hUnique U).mp hValue
  let p : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  let roots : Fin m → V := fun i => t (Fin.castAdd q.size i)
  have hRoots : Set.range roots ⊆ S := by
    rintro y ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hr j
    have hArg : xs i ∈ S := hXs i
    rw [hArgs i] at hArg
    simpa only [roots, hi] using hArg
  have hHull :
      UClosureHull (L.wholeMaskClosureRules P) C (Set.range roots) ⊆ S :=
    UClosureHull_minimal (L.wholeMaskClosureRules P) C hUSub hRoots
  intro y hy
  rw [hOutput] at hy
  obtain ⟨j, hj⟩ := hy
  rw [hj]
  exact hHull
    (hNormal.completeOutput_mem_inputHull
      C hValid hPos p q t hGraph j)

/-- Exact two-way correspondence: final C's relative U-closed subsets
are the function-closed subsets of the ACTUAL genuine partial decoder.
No syntactic canonicality of the ambient OLD/tagged C is asserted. -/
theorem wholeMaskCovered_USubstructure_iff_decodedClosed
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V) :
    IsUSubstructure (L.wholeMaskClosureRules P) C S ↔
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S := by
  exact ⟨wholeMaskCovered_USubstructure_to_decodedClosed
      C Base part hC hPos hCover S,
    wholeMaskCovered_decodedClosed_to_USubstructure
      C Base part hC hPos hCover S⟩

/-- The induced relational tagged test on exact S is intrinsically
U-closed iff S is closed under the ACTUAL decoded functions. -/
theorem wholeMaskCovered_inducedUClosed_iff_decodedClosed
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V) :
    IsUClosed (L.wholeMaskClosureRules P) (C.induce S) ↔
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S :=
  (hC.induce_iff_USubstructure S).trans
    (wholeMaskCovered_USubstructure_iff_decodedClosed
      C Base part hC hPos hCover S)

end StructuralRamsey.RelStructure
