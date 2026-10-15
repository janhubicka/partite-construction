import PartiteConstruction.Functional.EmptyRootGeneratorBudget
import PartiteConstruction.Functional.EHNIrreducibleRootOriginalPartialCompletion

/-!
# Full-functional native mixed attachments with EMPTY closed separator

A genuinely mixed closed source test is a FULL functional free amalgam of
its two closed pullback sides. If the exact common separator is empty,
the generator budget of the full test automatically bounds BOTH sides,
without any extra closure vertices or lower-rank induction.

If the separator has its prescribed FULL embedding q into Base, and both
sides have their own rank-n original-partial strict B-tree completions,
then synchronize the two completions by strictly attaching the SAME
prescribed Base-copy to each independent side tree over the EMPTY root.
The resulting two relative strict-tree extensions share the identical
root completion. This is stronger than an absolute tree completion:
it supplies precisely the root-relative witness requested by the
maximal-mixed attachment schema.

For an ACTUAL native EHN binary attachment the empty closed separator
has a canonical EHN projection to the selected A, and being empty is
irreducible. Hence this projection is a full embedding into A, and
composition with A ↪ Base gives the required prescribed root map.

Thus the EMPTY-SEPARATOR subcase of the maximal mixed strict functional
iteration is entirely discharged under its existing side rank-n
invariants. A nonempty reducible root is still not treated.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {C D VB : Type v}

/-- The strict original-partial generator-rank local-tree invariant
pulls back along a FULL embedding, without enlarging any source
closed test or changing its generator-size budget. -/
theorem LocallyGeneratedOriginalPartialTreeCompletable.pullback_embedding
    {Base : Structure L VB} {Old : Structure L D}
    {New : Structure L C} {n : ℕ}
    (hOld : LocallyGeneratedOriginalPartialTreeCompletable Base Old n)
    (e : Embedding New Old) :
    LocallyGeneratedOriginalPartialTreeCompletable Base New n := by
  classical
  intro S hS hGen
  let inc : Embedding (New.induce S hS) New :=
    inclusion New S hS
  exact hOld.completion_of_embedding
    (New.induce S hS) hGen (e.comp inc)

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C VB : Type v}

/-- A mixed full-functional free amalgam over the EMPTY common root
has two compatible original-partial strict B-tree relative
completions, provided each entire side is locally rank-n completable
and the source is n-generated.

This uses NO root-isolation hypothesis on partial maps and NO bound
on the cardinality of the function-closed hull of a weak image. -/
theorem compatibleOriginalPartialRelativeCompletions_empty_root
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite H] [Finite E] [Finite F] [IsEmpty H]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (Base : Structure L VB) (hBase : Base.Irreducible)
    (q : Embedding Root Base)
    (n : ℕ)
    (hWholeGen : Whole.GeneratedByAtMost n)
    (hLeftRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Left n)
    (hRightRank : LocallyGeneratedOriginalPartialTreeCompletable
      Base Right n) :
    HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sL q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base sR q := by
  classical
  obtain ⟨hLeftGen, hRightGen⟩ :=
    hFree.sides_generatedByAtMost_of_empty_root hWholeGen
  have hRoot : Root.Irreducible := irreducible_of_isEmpty Root
  have hLeft : HasOriginalPartialTreeCompletion Base Left :=
    hLeftRank.completion_of_embedding
      Left hLeftGen (Embedding.id Left)
  have hRight : HasOriginalPartialTreeCompletion Base Right :=
    hRightRank.completion_of_embedding
      Right hRightGen (Embedding.id Right)
  exact ⟨
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sL q hLeft,
    HasOriginalPartialTreeExtensionCompletion.of_irreducible_root_absolute
      Base hBase hRoot sR q hRight⟩

end StructuralRamsey.Structure.IsFreeAmalgam

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- The maximal-mixed-root schema is AUTOMATIC on those exact native
closed-test pullbacks whose common full-functional separator is EMPTY.

The two side generator budgets come from the full test, not from
counting the possibly much larger closed hull of projected generators.
The common rooted completion is the ACTUAL prescribed selected Base-copy,
with the exact EHN A-labels of the empty separator.

Unlike the weaker mere-full-completion statement, the conclusion
returns both compatible strict relative extensions required by the
maximal-mixed lemma; no separate root synchronization is assumed. -/
theorem native_closedTest_emptyRoot_compatibleRelativeCompletions
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (Base : Structure L VB)
    [Finite V] [Finite W]
    (hBase : Base.Irreducible)
    (eAB : Structure.Embedding A Base)
    (alpha : Structure.Embedding A Douter)
    (Dsys : System L P W)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)) Dsys)
    (Test : Set
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.IsClosed Test)
    (n : ℕ)
    (hWholeGen :
      ((UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.induce Test hTest).GeneratedByAtMost n)
    (hCore : LocallyGeneratedOriginalPartialTreeCompletable
      Base Dsys.toStructure n)
    (hCopy : LocallyGeneratedOriginalPartialTreeCompletable
      Base B.toStructure n)
    (hRootEmpty :
      let pb := closedTestPullback B
        (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f Test hTest
      IsEmpty pb.Common) :
    let pb := closedTestPullback B
      (B.support alpha.toFunctionEmbedding)
      (B.weak_support_closed Douter hB.1 A alpha)
      Dsys f Test hTest
    ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
      TreeAmalgam Base G Start ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toLeft q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Start) Base pb.toRight q := by
  classical
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  letI : IsEmpty pb.Common := hRootEmpty
  letI : Finite (Structure.Attachment.Vertex Supp
      (W := W) (I := PUnit.{v+1})) := inferInstance
  letI : Finite Test :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite pb.Left :=
    Finite.of_injective pb.leftIn pb.leftIn.injective
  letI : Finite pb.Right :=
    Finite.of_injective pb.rightIn pb.rightIn.injective
  letI : Finite pb.Common :=
    Finite.of_injective pb.toLeft pb.toLeft.injective
  let WR := B.weakRestrict Douter hB.1 A alpha
  have hRoot : pb.common.Irreducible :=
    irreducible_of_isEmpty pb.common
  have hRootEHN : pb.common.IsEHNHomomorphismEmbedding A
      (WR.part ∘ pb.commonMap) :=
    closedTestPullback_common_EHN
      B Douter hB A alpha Dsys f Test hTest
  obtain ⟨qA, _hQA⟩ :=
    hRootEHN.2 pb.common hRoot (Structure.Embedding.id pb.common)
  let q : Structure.Embedding pb.common Base := eAB.comp qA
  have hCoreSmall : LocallyGeneratedOriginalPartialTreeCompletable
      Base pb.left n :=
    hCore.pullback_embedding pb.leftMap
  have hCopySmall : LocallyGeneratedOriginalPartialTreeCompletable
      Base pb.right n :=
    hCopy.pullback_embedding pb.rightMap
  obtain ⟨hLeft, hRight⟩ :=
    pb.free.compatibleOriginalPartialRelativeCompletions_empty_root
      Base hBase q n hWholeGen hCoreSmall hCopySmall
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Structure.Embedding.id Base)
      (fun x => ⟨x, rfl⟩)
  exact ⟨VB, Base, q, hTree, hLeft, hRight⟩

end StructuralRamsey.FunctionalPartite.Attachment
