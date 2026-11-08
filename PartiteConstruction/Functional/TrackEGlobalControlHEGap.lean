import PartiteConstruction.Functional.TrackEExactThreeClauseEndgame
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff

/-!
# Track E: the control map must be checked as a homomorphism-embedding

The two-pass corrected 2019 actual native sparse-witness theorem exports
a global 2019 SOURCE-DEFINED PARTIAL HOMOMORPHISM. The original printed
first clause asks for a homomorphism-EMBEDDING, requiring the IDENTICAL
map to restrict to a full embedding of every genuine irreducible test.

We isolate the precise logical nonimplication on an ACTUAL corrected
finite Ramsey witness, even with INTERNAL B-copy coverage, a genuine
loose full-functional B-tree, and EVEN another good EHN/2019-HE map
to the same control structure.

For the binary left-projection D=Fin 3, the CONSTANT map q=0 is always
an original source-defined partial homomorphism from any native C:
each defined source fibre is nonempty and its whole image is {0}.
But q is not a HE whenever C contains a genuine full B=Fin 2 copy,
because the whole irreducible B would have to embed constantly in D.

This does NOT refute the specially chosen 2019 control projection's
potential HE property. It prevents inferring that property from merely
the PARTIAL homomorphism statement, Ramsey, or B-copy coverage.
No strict functional-tree statement, new axiom or manuscript edit.
-/

namespace StructuralRamsey.Structure.TrackEGlobalControlHEGap

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.PublishedTotalBinaryObstruction
open StructuralRamsey.Structure.TrackEExactThreeClauseEndgame
open StructuralRamsey.Structure.TrackESourceDefinedPartialIff

/-- The constant-zero projection into the total binary left-projection
control D satisfies the genuine 2019 source-defined whole-fibre
homomorphism law for EVERY C in the same language. It imposes no
condition on source-undefined input tuples. -/
theorem constant_projection_is_originalPartialHom
    {X : Type} (C : Structure language X) :
    IsOriginalPartialHomomorphism C D (fun _ : X => (0 : Fin 3)) := by
  constructor
  · intro R
    exact Empty.elim R
  · intro F xs hDefined
    change (C.func F xs).Nonempty at hDefined
    change imageSet (fun _ : X => (0 : Fin 3)) (C.func F xs) =
      ({0} : Set (Fin 3))
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rfl
    · intro hy
      change y = (0 : Fin 3) at hy
      subst y
      obtain ⟨z, hz⟩ := hDefined
      exact ⟨z, hz, rfl⟩

/-- On the SAME constant map, full irreducible-copy reflection fails
as soon as C contains one genuine full copy of the 2-point B.
The failure occurs in the HE condition, NOT the source-defined
whole-fibre homomorphism condition. -/
theorem constant_projection_not_originalPartialHE_of_Bcopy
    {X : Type} (C : Structure language X)
    (e : Embedding B C) :
    ¬ IsOriginalPartialHomomorphismEmbedding C D
      (fun _ : X => (0 : Fin 3)) := by
  intro hHE
  have hBIrr : B.Irreducible :=
    total_irreducible (algebra_total (Fin 2))
  obtain ⟨g, hg⟩ := hHE.2 B hBIrr e
  have hg0 : g (0 : Fin 2) = (0 : Fin 3) := hg 0
  have hg1 : g (1 : Fin 2) = (0 : Fin 3) := hg 1
  have hEq : (0 : Fin 2) = 1 :=
    g.injective (hg0.trans hg1.symm)
  exact (by decide : (0 : Fin 2) ≠ 1) hEq

/-- An actual 2-colour Ramsey arrow guarantees at least one real
full B-copy, hence the constant original-partial control map can
never be a HE, even before imposing the final internal B coverage. -/
theorem constant_projection_not_originalPartialHE_of_Ramsey
    {X : Type} (C : Structure language X)
    (hArrow : Arrow A B C (Fin 2)) :
    ¬ IsOriginalPartialHomomorphismEmbedding C D
      (fun _ : X => (0 : Fin 3)) := by
  obtain ⟨e, _⟩ :=
    hArrow (fun _ : Embedding A C => (0 : Fin 2))
  exact constant_projection_not_originalPartialHE_of_Bcopy C e

/-- Non-vacuous counterexample on an ACTUAL already-verified corrected
finite Ramsey witness: the SAME C admits both
(a) a GOOD original-2019 homomorphism-embedding p, and
(b) a BAD source-defined partial homomorphism q into the SAME D
    that is not a HE.
Moreover C has internal B-copy extension and is a true loose
functional B-tree. Thus any control-map HE upgrade must be proven
about the PARTICULAR selected p, not inferred from these witness
properties or the existence of some other good map. -/
theorem actual_Ramsey_Bcovered_goodHE_and_badHom_same_C :
    ∃ (X : Type) (_ : Finite X) (C : Structure language X),
      Arrow A B C (Fin 2) ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B X C ∧
      (∃ p : X → Fin 3,
        IsOriginalPartialHomomorphismEmbedding C D p) ∧
      (∃ q : X → Fin 3,
        IsOriginalPartialHomomorphism C D q ∧
        ¬ IsOriginalPartialHomomorphismEmbedding C D q) := by
  obtain ⟨X, hX, C, hArrow, hCover, hLoose, p, hp, _hLoss⟩ :=
    actual_corrected_Bcovered_RamseyWitness_loses_domain
  exact ⟨X, hX, C, hArrow, hCover, hLoose,
    ⟨p, hp⟩, ⟨(fun _ => (0 : Fin 3)),
      constant_projection_is_originalPartialHom C,
      constant_projection_not_originalPartialHE_of_Ramsey C hArrow⟩⟩

/-- The same difference persists in canonical genuine `Option(Set)`
syntax: the BAD map satisfies the genuine source-defined homomorphism
predicate but fails the faithful native-irreducible-copy HE predicate
from the verified same-map Track E correspondence. -/
theorem actual_bad_projection_genuinePartialHom_not_canonicalHE :
    ∃ (X : Type) (_ : Finite X) (C : Structure language X),
      Arrow A B C (Fin 2) ∧
      IrreduciblesExtendTo B C ∧
      ∃ q : X → Fin 3,
        PartialSetStructure.IsOriginalPartialHomomorphism
          C.toNonemptyPartial D.toNonemptyPartial q ∧
        ¬ CanonicalEncodedOriginalPartialHE C D q := by
  obtain ⟨X, hX, C, hArrow, hCover, _hLoose, _hGood, q, hHom, hNotHE⟩ :=
    actual_Ramsey_Bcovered_goodHE_and_badHom_same_C
  refine ⟨X, hX, C, hArrow, hCover, q,
    (originalPartialHom_iff_nonemptyPartial.mp hHom), ?_⟩
  intro hEncoded
  exact hNotHE
    (originalPartialHE_iff_canonicalEncodedHE.mpr hEncoded)

end StructuralRamsey.Structure.TrackEGlobalControlHEGap
