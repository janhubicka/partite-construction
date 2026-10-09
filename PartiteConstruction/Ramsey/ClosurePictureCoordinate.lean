import PartiteConstruction.Ramsey.ClosurePictureRetraction
import PartiteConstruction.Ramsey.ClosureAttachmentSubhistory
import PartiteConstruction.Partite.Induced

/-! # Native Hales--Jewett coordinates reuse the old rank invariant

A coordinate that is variable on each exterior line met by the GENERATORS
of a tested structure gives a protected retraction of the required
subattachment to the old picture. Thus the old rank-n invariant completes
that test without a smaller absolute side-rank assumption.

In particular, the case of generators meeting at most one exterior line
is complete, including tests with additional vertices anywhere in the core.
Whole-picture closedness and the protected core projection are explicit
construction invariants. They are not inferred from an arbitrary ordinary
partite system. The no-common-coordinate case is not asserted here.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P Q V I X : Type v} {N : ℕ}

/-- Coordinate evaluation of the native induced power is positive. -/
theorem coordinate_homomorphism (B : System L P V) (k : Fin N) :
    (power B N).toRelStructure.IsHomomorphism B.toRelStructure
      (fun x => x.coord k) := by
  intro R z hz
  exact hz k

/-- Coordinate evaluation is a protected map when the power's part
projection is protected and the old part projection is positive. -/
theorem coordinate_closedMap
    {rules : ClosureDescription L} {A : RelStructure L P}
    (B : System L P V) (k : Fin N)
    (hB : B.toRelStructure.IsHomomorphism A B.part)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power B N).toRelStructure A (power B N).part) :
    IsClosedUHomomorphismEmbedding rules (power B N).toRelStructure
      B.toRelStructure (fun x => x.coord k) := by
  have hEq : B.part ∘ (fun x : Vertex B N => x.coord k) =
      (power B N).part := by
    funext x
    exact x.belongs k
  apply IsClosedUHomomorphismEmbedding.of_comp_homomorphisms
    (coordinate_homomorphism B k) hB
  rw [hEq]
  exact hPower

/-- A variable coordinate is a left inverse of its native line map. -/
theorem coordinate_lineMap_parameter
    {A : RelStructure L P} {B : System L P V}
    (line : Line (Letter A B) N) (k : Fin N)
    (hk : line.symbol k = .parameter) (x : V) :
    (NonInduced.lineMap line x).coord k = x := by
  simp only [NonInduced.lineMap, hk]

/-- The selected lines use the existing native induced line embeddings
of the restricted old system; no surrogate core is introduced. -/
noncomputable def closureLineMaps
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N) :
    I → RelStructure.Embedding
      (Old.toRelStructure.induce (Old.support alpha))
      (power (Old.restrict alpha) N).toRelStructure :=
  fun i => (lineEmbedding hRestricted (lines i)).toEmbedding

/-- Generators whose exterior lines share a variable coordinate are
completed using the previous old-picture rank invariant. The exact test
factors into its selected subfamily; other lines in the full Picture
need NOT share the coordinate. -/
theorem completion_of_common_generator_coordinate
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
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
    (hSize : G.card ≤ n) (k : Fin N)
    (hActive : ∀ g ∈ G, ∀ i,
      RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
        (lines i).symbol k = .parameter) :
    HasClosedUKCompletion K rules Test := by
  classical
  let R := Old.restrict alpha
  let Core := (power R N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let J : Set I := {i | (lines i).symbol k = .parameter}
  obtain ⟨d, _⟩ := RelStructure.Attachment.factor_through_generator_subfamily
    Old.toRelStructure (Old.support alpha) Core maps hSupport Test e
    (↑G : Set X) hGen J hActive
  have hSubClosed : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        Core (fun i : J => maps i.1)) :=
    RelStructure.Attachment.subfamily_isUClosed
      Old.toRelStructure (Old.support alpha) Core maps hSupport hWhole J
  let r : Vertex R N → V := fun x => (x.coord k).1
  have hr : IsClosedUHomomorphismEmbedding rules Core Old.toRelStructure r :=
    ((RelStructure.inclusion Old.toRelStructure (Old.support alpha)).isClosedUHomomorphismEmbedding rules).comp
      (coordinate_closedMap R k hRestricted.1 hPower)
  have hInverse : ∀ i : J, ∀ x : Old.support alpha,
      r (maps i.1 x) = x.1 := by
    intro i x
    change ((NonInduced.lineMap (lines i.1) x).coord k).1 = x.1
    rw [coordinate_lineMap_parameter (lines i.1) k i.2 x]
  exact RelStructure.Attachment.completion_from_old_rank_via_retraction
    Old.toRelStructure (Old.support alpha) Core (fun i : J => maps i.1)
    hOld hSupport hSubClosed r hr hInverse n hRank Test d G hGen hSize

/-- Requiring one globally common parameter coordinate would destroy the
Ramsey line property: the colouring by that coordinate splits every line.
Therefore the common-coordinate hypothesis above must remain LOCAL to
one test's exterior lines, not imposed on the whole Ramsey family. -/
theorem no_monochromatic_line_with_fixed_parameter
    {Alphabet : Type v} (lines : I → Line Alphabet N)
    (k : Fin N) (hCommon : ∀ i, (lines i).symbol k = .parameter)
    (a b : Alphabet) (hab : a ≠ b) :
    ¬ ∃ i, ∀ x y : Alphabet, ((lines i).eval x) k = ((lines i).eval y) k := by
  rintro ⟨i, hMono⟩
  apply hab
  simpa only [Line.eval, LineSymbol.eval, hCommon i] using hMono a b

end StructuralRamsey.Partite.Induced
