import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam
import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.EHNAttachmentDecompose

/-!
# Weak vertex-exact tests of a genuine native EHN functional attachment

The iterated sparsening proof tests arbitrary WEAK substructures, not
their function-closed hulls. A native EHN binary Picture attachment
is an actual full functional free amalgam over the selected CLOSED
support. Its arbitrary weak test therefore decomposes exactly as
the free amalgam of the weak core, weak copied old picture, and the
actual weak common root.

This module uses no surrogate relational Picture. Each side and the
whole test interpret genuine set-valued functions, and the whole
weak test remains FUNCTION-OUTPUT TRANSVERSAL in its partite system:
distinct outputs of one input in the same part coincide.

Moreover, for a genuinely mixed test, each side preimage has
strictly fewer vertices than the whole weak test, WITHOUT assuming
the test is closed. This is the correct induction-size bookkeeping
for the published two-case iteration.

The structural decomposition does NOT assert the missing geometric
existence of compatible relative strict B-tree completions of the
weak common root. That is the remaining mixed-case obligation.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- For ANY finite exact vertex set of a functional free amalgam,
a vertex outside the left side gives a strict decrease of the left
preimage cardinality. Unlike the old closed-test lemma, there is
no function-closedness assumption whatsoever. -/
theorem weakLeftPreimage_card_lt
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (_hFree : IsFreeAmalgam sL sR iL iR)
    (Test : Set C) [Fintype Test] [Fintype (iL ⁻¹' Test)]
    (z : Test) (hz : ¬ ∃ a : E, z.1 = iL a) :
    Fintype.card (iL ⁻¹' Test) < Fintype.card Test := by
  let j : (iL ⁻¹' Test) → Test :=
    fun x => ⟨iL x.1, x.2⟩
  apply Fintype.card_lt_of_injective_not_surjective j
  · intro x y hxy
    apply Subtype.ext
    apply iL.injective
    exact congrArg Subtype.val hxy
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj z
    apply hz
    exact ⟨x.1, (congrArg Subtype.val hx).symm⟩

/-- Symmetric right-preimage decrease for arbitrary weak vertex
subsets, with no extra closure vertices and no original-domain
reflection. -/
theorem weakRightPreimage_card_lt
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (_hFree : IsFreeAmalgam sL sR iL iR)
    (Test : Set C) [Fintype Test] [Fintype (iR ⁻¹' Test)]
    (z : Test) (hz : ¬ ∃ b : F, z.1 = iR b) :
    Fintype.card (iR ⁻¹' Test) < Fintype.card Test := by
  let j : (iR ⁻¹' Test) → Test :=
    fun x => ⟨iR x.1, x.2⟩
  apply Fintype.card_lt_of_injective_not_surjective j
  · intro x y hxy
    apply Subtype.ext
    apply iR.injective
    exact congrArg Subtype.val hxy
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj z
    apply hz
    exact ⟨x.1, (congrArg Subtype.val hx).symm⟩

end StructuralRamsey.Structure.IsFreeAmalgam

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

noncomputable section

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- The literal full-functional weak core/copy/root decomposition of
an arbitrary exact vertex test of ONE ACTUAL EHN binary attachment,
together with output transversality of its weak whole test.

All four canonical maps are FULL embeddings of the WEAK function
structures; their ranges and vertices agree with the original
attachment on the nose, and no function closure is added. -/
theorem unit_weakTest_decompose_transversal
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1}))) :
    let coreSet : Set W :=
      (unitCoreEmbedding B S hS D f) ⁻¹' Test
    let copySet : Set V :=
      (unitCopyEmbedding B S hS D f) ⁻¹' Test
    let rootSet : Set S :=
      ((unitCoreEmbedding B S hS D f).comp f.toEmbedding) ⁻¹' Test
    ∃ (mCore : Embedding
        ((B.induce S hS).toStructure.weakInduce rootSet)
        (D.toStructure.weakInduce coreSet))
      (mCopy : Embedding
        ((B.induce S hS).toStructure.weakInduce rootSet)
        (B.toStructure.weakInduce copySet))
      (jCore : Embedding (D.toStructure.weakInduce coreSet)
        ((UnitAttachD B S hS D f).toStructure.weakInduce Test))
      (jCopy : Embedding (B.toStructure.weakInduce copySet)
        ((UnitAttachD B S hS D f).toStructure.weakInduce Test)),
      IsFreeAmalgam mCore mCopy jCore jCopy ∧
      (∀ x : coreSet, (jCore x).1 = unitCoreEmbedding B S hS D f x.1) ∧
      (∀ x : copySet, (jCopy x).1 = unitCopyEmbedding B S hS D f x.1) ∧
      (∀ F (x : Fin (L.funcArity F) → Test),
        Set.InjOn ((UnitAttachD B S hS D f).weakInduce Test).part
          (((UnitAttachD B S hS D f).weakInduce Test).func F x)) := by
  classical
  dsimp only
  obtain ⟨mCore, mCopy, jCore, jCopy, hFree, hCore, hCopy⟩ :=
    (unit_isFreeAmalgam_full B S hS D f).weakInduce_withMaps Test
  refine ⟨mCore, mCopy, jCore, jCopy, hFree, hCore, hCopy, ?_⟩
  intro F x
  exact ((UnitAttachD B S hS D f).weakInduce Test).func_part_injOn F x

/-- The exact weak core has strictly fewer vertices when the test
contains a point outside the attached core. In contrast to the
earlier closed-only cardinality lemma this uses NO closure
hypothesis on Test. -/
theorem unit_weakTest_corePreimage_card_lt
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    [Fintype Test]
    [Fintype ((unitCoreEmbedding B S hS D f) ⁻¹' Test)]
    (z : Test)
    (hz : ¬ ∃ w : W, z.1 = unitCoreEmbedding B S hS D f w) :
    Fintype.card ((unitCoreEmbedding B S hS D f) ⁻¹' Test) <
      Fintype.card Test :=
  (unit_isFreeAmalgam_full B S hS D f).weakLeftPreimage_card_lt
    Test z hz

/-- The copied-old-picture weak side is likewise strictly smaller
when the mixed test has a point outside that side. -/
theorem unit_weakTest_copyPreimage_card_lt
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (Test : Set (Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1})))
    [Fintype Test]
    [Fintype ((unitCopyEmbedding B S hS D f) ⁻¹' Test)]
    (z : Test)
    (hz : ¬ ∃ x : V, z.1 = unitCopyEmbedding B S hS D f x) :
    Fintype.card ((unitCopyEmbedding B S hS D f) ⁻¹' Test) <
      Fintype.card Test :=
  (unit_isFreeAmalgam_full B S hS D f).weakRightPreimage_card_lt
    Test z hz

end StructuralRamsey.FunctionalPartite.Attachment
