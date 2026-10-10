import PartiteConstruction.Ramsey.ClosurePictureCoordinate

/-! # Explicit solved branches of the Hales--Jewett rank increment

The verified coordinate-retraction theorem already completes a test
whose generator-active exterior lines share a variable coordinate.
A *single* active exterior line always has such a coordinate, even if
every OTHER line in the full Ramsey family has a conflicting parameter
set. The case with no exterior generators is likewise vacuous for
any coordinate in a positive power.

These corollaries avoid a global common-parameter assumption (which is
incompatible with the Hales--Jewett Ramsey property). They isolate the
unresolved branch: at least TWO generator-active exterior lines with
no shared parameter coordinate. Neither corollary is a j->j+1 proof.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V I X : Type v} {N : ℕ}

/-- If every exterior line met by a generating set is the SAME line
i0, choose one of that line's parameter coordinates and retract the
relevant subattachment to Old. The full family may have other lines
with no common variable coordinate whatsoever. -/
theorem completion_of_single_generator_line
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ n →
        HasClosedUKCompletion K rules (Old.toRelStructure.induce T))
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n)
    (i0 : I)
    (hOnlyLine : ∀ g ∈ G, ∀ i,
      RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
        i = i0) :
    HasClosedUKCompletion K rules Test := by
  obtain ⟨k, hk⟩ := (lines i0).hasParameter
  apply completion_of_common_generator_coordinate
    Old alpha A hRestricted lines hOld hSupport hPower hWhole
    n hRank Test e G hGen hSize k
  intro g hg i hOutside
  rw [hOnlyLine g hg i hOutside]
  exact hk

/-- If NO generator lies outside the core, any coordinate of a
positive native power provides the required retraction. The test
may contain additional nongenerating vertices in exterior copies:
the factor-through-generator-subfamily lemma handles them. -/
theorem completion_of_no_generator_lines
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (hN : 0 < N)
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ n →
        HasClosedUKCompletion K rules (Old.toRelStructure.induce T))
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n)
    (hNoOutside : ∀ g ∈ G, ∀ i,
      ¬ RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g)) :
    HasClosedUKCompletion K rules Test := by
  let k : Fin N := ⟨0, hN⟩
  apply completion_of_common_generator_coordinate
    Old alpha A hRestricted lines hOld hSupport hPower hWhole
    n hRank Test e G hGen hSize k
  intro g hg i hOutside
  exact False.elim (hNoOutside g hg i hOutside)

end StructuralRamsey.Partite.Induced
