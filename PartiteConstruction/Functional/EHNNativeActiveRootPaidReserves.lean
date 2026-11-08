import PartiteConstruction.Functional.EHNActiveGeneratedHardRootRelative
import PartiteConstruction.Functional.MultiGeneratedIrreducibleRootReserves

/-!
# Track D: ACTUAL native active root + PAID exterior generator reserves

The newly isolated active-generated hard-root condition proves that an
actual closed `closedTestPullback` separator is irreducible and
FULLY maps into the selected A. The existing native source-side
rank argument, however, does NOT automatically bound the generator
ranks of the two closed pullback sides. Simply charging the whole
root closure by its vertex cardinality is false.

This module combines that active-generated-root fact with the
verified genuine functional mixed EXTERIOR generator-reserve budget.
Given an actual finite generating set G of the exact whole closed
test and a generating set Roots of the actual common root, suppose
that |Roots| distinct elements of G are OUTSIDE the core and
|Roots| distinct elements of G are OUTSIDE the copied old side.
Then the two closed tested sides automatically have generator
rank <=n, where n bounds |G|, even if the common root has
arbitrarily many function-generated vertices.

The actual old-side/core predecessor rank-n strict tree invariants
therefore complete both sides absolutely, and irreducibility of the
active-generated separator synchronizes their completions RELATIVELY
over the SAME canonical full A-to-Base map.

This genuinely advances the full-function original-2019 mixed case
for actual native attachments with multi-generated active roots and
enough exterior generator reserves. It does NOT assert that any
actual multi-line Hales--Jewett history supplies the reserves, or
that every hard root is active-generated. The original full
function structures, exact tested vertex sets and source-defined
partial-function semantics are preserved.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V W VB : Type v}

/-- A genuine native one-copy EHN closed attachment has two
compatible original-partial STRICT full-function Base-tree
extensions over the SAME selected A root, under concrete
active-root and PAID exterior-generator hypotheses.

Unlike the earlier active-root result, NO generator-rank
hypothesis on the new tested sides is separately assumed:
both rank bounds are derived from one literal whole-test
generating set G and root/exterior generator reserves.

The chosen side exterior sets may differ; they must be
subsets of G and pay at least the chosen number of ROOT
generator seeds on each side independently. -/
theorem native_closedTest_activeGeneratedRoot_paidReserves_relative
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
    (hCore : LocallyGeneratedOriginalPartialTreeCompletable
      Base Dsys.toStructure n)
    (hCopy : LocallyGeneratedOriginalPartialTreeCompletable
      Base B.toStructure n)
    (hData :
      let Supp := B.support alpha.toFunctionEmbedding
      let hSupp := B.weak_support_closed Douter hB.1 A alpha
      let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
      ∃ (G : Finset Test)
        (Roots : Finset pb.Common)
        (OutRight OutLeft : Finset Test)
        (Func : L.FuncSymbol)
        (xs : Fin (L.funcArity Func) → pb.Common)
        (y : pb.Common),
        ((UnitAttachD B Supp hSupp Dsys f).toStructure.induce
          Test hTest).GeneratedBy (↑G : Set Test) ∧
        G.card ≤ n ∧
        pb.common.GeneratedBy (↑Roots : Set pb.Common) ∧
        pb.common.GeneratedBy (Set.range xs) ∧
        y ∈ pb.common.func Func xs ∧
        OutRight ⊆ G ∧
        (∀ z ∈ OutRight, z ∉ Set.range pb.leftIn) ∧
        Roots.card ≤ OutRight.card ∧
        OutLeft ⊆ G ∧
        (∀ z ∈ OutLeft, z ∉ Set.range pb.rightIn) ∧
        Roots.card ≤ OutLeft.card) :
    let Supp := B.support alpha.toFunctionEmbedding
    let hSupp := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
    ∃ (q : Structure.Embedding pb.common Base),
      (∀ x : pb.Common,
        q x = eAB ((B.weakRestrict Douter hB.1 A alpha).part
          (pb.commonMap x))) ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toLeft q ∧
      HasOriginalPartialTreeExtensionCompletion
        (Start := Base) Base pb.toRight q := by
  classical
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
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
  obtain ⟨G, Roots, OutRight, OutLeft, Func, xs, y,
    hWholeGen, hGcard, hRootGen, hActiveGen, hy,
    hOutRightSub, hOutRightExterior, hOutRightPays,
    hOutLeftSub, hOutLeftExterior, hOutLeftPays⟩ := hData
  have hRoot : pb.common.Irreducible :=
    irreducible_of_generated_by_defined_function
      pb.common Func xs hActiveGen hy
  let WR := B.weakRestrict Douter hB.1 A alpha
  have hRootEHN : pb.common.IsEHNHomomorphismEmbedding A
      (WR.part ∘ pb.commonMap) :=
    closedTestPullback_common_EHN
      B Douter hB A alpha Dsys f Test hTest
  have hCoreLocal : LocallyGeneratedOriginalPartialTreeCompletable
      Base pb.left n :=
    hCore.pullback_embedding pb.leftMap
  have hCopyLocal : LocallyGeneratedOriginalPartialTreeCompletable
      Base pb.right n :=
    hCopy.pullback_embedding pb.rightMap
  obtain ⟨q, hCanonical, hRelL, hRelR⟩ :=
    pb.free.compatibleOriginalPartialRelativeCompletions_irr_EHN_root_reserves
      A Base hBase hRoot
      (WR.part ∘ pb.commonMap) hRootEHN eAB
      n G hWholeGen hGcard Roots hRootGen
      OutRight hOutRightSub hOutRightExterior hOutRightPays
      OutLeft hOutLeftSub hOutLeftExterior hOutLeftPays
      hCoreLocal hCopyLocal
  exact ⟨q, hCanonical, hRelL, hRelR⟩

end StructuralRamsey.FunctionalPartite.Attachment
