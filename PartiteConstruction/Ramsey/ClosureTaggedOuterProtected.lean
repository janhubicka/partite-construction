import PartiteConstruction.Ramsey.ClosureTaggedOuterDescent

/-! # The protected OUTER projection comes from old-copy coverage

The unrestricted recursive little Picture O may have conflicting
closure outputs. Thus its ordinary partite projection to D does NOT
by itself show that a closed U-irreducible test in the new witness
maps as an induced embedding to D.

Instead use the inner tagged relative-copy theorem's COVERAGE:
every closed U-tagged-irreducible test in the closed new tagged
witness T embeds into the original OLD tagged picture. The target
old picture already has a protected closed-test projection to D.

Normalize T by its protected map into the little Picture (#197),
then expand any exact closed irreducible old-language test to T,
use tagged coverage, and forget its part-preserving embedding
into Old. These copies have the SAME OUTER part labels. Composing
with Old's protected map gives the required protected projection
of the new outer D-partite picture.

No global U-closedness of the temporary O, no target closure hull,
and no hypothetical K-completion are used.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}} {P V W Y X : Type v}

/-- Actual tagged closed-test coverage gives an embedding of each
old-language closed irreducible test into the ORIGINAL Old picture,
respecting exactly the outer part labels. The exact source test
is not replaced by a closure hull. -/
theorem taggedWitnessOuter_closedTest_in_old
    {rules : ClosureDescription L}
    (D : RelStructure L P) (Old : System L P V)
    (O : System L P W)
    (T : System (L.withTaggedClosureParts rules P) W Y)
    (hT : IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure)
    (hProj : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T.toRelStructure
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      T.part)
    (hOPart : O.IsPartiteOver D)
    (hCover : ∀ {Z : Type v}
        (Test : RelStructure (L.withTaggedClosureParts rules P) Z),
        IsUClosed (rules.withTaggedClosureParts P) Test →
        IsUIrreducible (rules.withTaggedClosureParts P) Test →
        RelStructure.Embedding Test T.toRelStructure →
        Nonempty (RelStructure.Embedding Test
          (RelStructure.expandTaggedClosureParts rules
            Old.toRelStructure Old.part)))
    (Test : RelStructure L X)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : RelStructure.Embedding Test
      (taggedWitnessOuterSystem rules D O T hT hProj hOPart).toRelStructure) :
    ∃ g : RelStructure.Embedding Test Old.toRelStructure,
      ∀ x, Old.part (g x) =
        (taggedWitnessOuterSystem rules D O T hT hProj hOPart).part (e x) := by
  let C := taggedWitnessOuterSystem rules D O T hT hProj hOPart
  let partTest : X → P := fun x => C.part (e x)
  have hNorm :
      T.toRelStructure =
        RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part :=
    tagged_closed_source_normalizes_of_protected
      rules T.toRelStructure O.toRelStructure O.part T.part hT hProj
  let eExpanded : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules Test partTest)
      (RelStructure.expandTaggedClosureParts rules C.toRelStructure C.part) :=
    e.expandTaggedClosureParts partTest C.part (fun _ => rfl)
  let eTag : RelStructure.Embedding
      (RelStructure.expandTaggedClosureParts rules Test partTest)
      T.toRelStructure := by
    rw [hNorm]
    exact eExpanded
  have hClosedTag : IsUClosed (rules.withTaggedClosureParts P)
      (RelStructure.expandTaggedClosureParts rules Test partTest) :=
    (isUClosed_iff_taggedParts rules Test partTest).mp hClosed
  have hIrredTag : IsUIrreducible (rules.withTaggedClosureParts P)
      (RelStructure.expandTaggedClosureParts rules Test partTest) :=
    (isUIrreducible_iff_taggedParts_of_closed rules Test partTest hClosed).mp hIrred
  obtain ⟨gTag⟩ := hCover
    (RelStructure.expandTaggedClosureParts rules Test partTest)
    hClosedTag hIrredTag eTag
  refine ⟨gTag.forgetTaggedClosureParts, ?_⟩
  intro x
  exact gTag.tagged_preserves_part x

/-- The descended outer D-projection protects ALL old-language closed
U-irreducible tests. The critical input is actual coverage by Old_tag,
not merely ordinary partiteness of the conflicting little Picture O. -/
theorem taggedWitnessOuter_protected
    {rules : ClosureDescription L}
    (D : RelStructure L P) (Old : System L P V)
    (O : System L P W)
    (T : System (L.withTaggedClosureParts rules P) W Y)
    (hT : IsUClosed (rules.withTaggedClosureParts P) T.toRelStructure)
    (hProj : IsClosedUHomomorphismEmbedding (rules.withTaggedClosureParts P)
      T.toRelStructure
      (RelStructure.expandTaggedClosureParts rules O.toRelStructure O.part)
      T.part)
    (hOPart : O.IsPartiteOver D)
    (hOldProtected :
      IsClosedUHomomorphismEmbedding rules Old.toRelStructure D Old.part)
    (hCover : ∀ {Z : Type v}
        (Test : RelStructure (L.withTaggedClosureParts rules P) Z),
        IsUClosed (rules.withTaggedClosureParts P) Test →
        IsUIrreducible (rules.withTaggedClosureParts P) Test →
        RelStructure.Embedding Test T.toRelStructure →
        Nonempty (RelStructure.Embedding Test
          (RelStructure.expandTaggedClosureParts rules
            Old.toRelStructure Old.part))) :
    IsClosedUHomomorphismEmbedding rules
      (taggedWitnessOuterSystem rules D O T hT hProj hOPart).toRelStructure
      D (taggedWitnessOuterSystem rules D O T hT hProj hOPart).part := by
  let C := taggedWitnessOuterSystem rules D O T hT hProj hOPart
  constructor
  · exact (taggedWitnessOuterSystem_isPartiteOver
      rules D O T hT hProj hOPart).1
  · intro Z Test hClosed hIrred e
    obtain ⟨gOld, hgPart⟩ :=
      taggedWitnessOuter_closedTest_in_old D Old O T hT hProj hOPart
        hCover Test hClosed hIrred e
    obtain ⟨j, hj⟩ := hOldProtected.on_test Test hClosed hIrred gOld
    refine ⟨j, ?_⟩
    intro x
    calc
      j x = Old.part (gOld x) := hj x
      _ = C.part (e x) := hgPart x

end StructuralRamsey.Partite.Induced
