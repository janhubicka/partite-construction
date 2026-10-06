import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.ClosedLocalTreeCompletion

/-! # Pure-side cases for one functional EHN attachment

The functional EHN Picture is built by repeated binary attachments.  For a
closed tested substructure of one such attachment, two cases are immediate:

* if the test lies wholly in the attached copy, factor it through the copy
  embedding and reuse the previous-stage local-tree witness;
* if the test lies wholly in the core, factor it through the core embedding
  and reuse the core local-tree witness.

Only the genuinely mixed case needs projected-history synchronization.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {P V W : Type v}

variable (B : System L P V)
variable (S : Set V) (hS : B.toStructure.IsClosed S)
variable (D : System L P W)
variable (f :
  FunctionalPartite.Embedding (B.induce S hS) D)

noncomputable abbrev UnitAttach :=
  attach B S hS D (fun _ : PUnit.{v+1} => f)

/-- A closed test lying wholly in the single attached copy factors fully back
into B. -/
noncomputable def testEmbeddingToCopy
    (Test : Finset (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttach B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (hcopy :
      ∀ z : ↥(↑Test : Set _),
        ∃ x : V,
          z.1 =
            Structure.Attachment.copyEmbedding
              B.toStructure S hS D.toStructure
              (fun _ : PUnit.{v+1} => f.toEmbedding)
              PUnit.unit x) :
    Structure.Embedding
      ((UnitAttach B S hS D f).toStructure.induce
        (↑Test : Set _) hTest)
      B.toStructure := by
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  let Small :=
    (UnitAttach B S hS D f).toStructure.induce TestSet hTest
  let incSmall : Structure.Embedding Small
      (UnitAttach B S hS D f).toStructure :=
    Structure.inclusion
      (UnitAttach B S hS D f).toStructure
      TestSet hTest
  let copyEmb : Structure.Embedding B.toStructure
      (UnitAttach B S hS D f).toStructure :=
    Structure.Attachment.copyEmbedding
      B.toStructure S hS D.toStructure
      (fun _ : PUnit.{v+1} => f.toEmbedding)
      PUnit.unit
  have hrange :
      ∀ z : ↥TestSet,
        ∃ x : V, incSmall z = copyEmb x := by
    intro z
    rcases hcopy z with ⟨x, hx⟩
    exact ⟨x, hx⟩
  exact incSmall.factorThroughClosedRange copyEmb hrange

/-- A closed test lying wholly in the core factors fully back into D. -/
noncomputable def testEmbeddingToCore
    (Test : Finset (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hTest : (UnitAttach B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (hcore :
      ∀ z : ↥(↑Test : Set _),
        ∃ w : W,
          z.1 =
            Structure.Attachment.coreEmbedding
              B.toStructure S hS D.toStructure
              (fun _ : PUnit.{v+1} => f.toEmbedding) w) :
    Structure.Embedding
      ((UnitAttach B S hS D f).toStructure.induce
        (↑Test : Set _) hTest)
      D.toStructure := by
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  let Small :=
    (UnitAttach B S hS D f).toStructure.induce TestSet hTest
  let incSmall : Structure.Embedding Small
      (UnitAttach B S hS D f).toStructure :=
    Structure.inclusion
      (UnitAttach B S hS D f).toStructure
      TestSet hTest
  let coreEmb : Structure.Embedding D.toStructure
      (UnitAttach B S hS D f).toStructure :=
    Structure.Attachment.coreEmbedding
      B.toStructure S hS D.toStructure
      (fun _ : PUnit.{v+1} => f.toEmbedding)
  have hrange :
      ∀ z : ↥TestSet,
        ∃ w : W, incSmall z = coreEmb w := by
    intro z
    rcases hcore z with ⟨w, hw⟩
    exact ⟨w, hw⟩
  exact incSmall.factorThroughClosedRange coreEmb hrange

/-- Pure-copy local-tree witness for one EHN attachment. -/
theorem pureCopy_locallyClosedTreeCompletable
    {VB : Type v} {Base : Structure L VB}
    (n : ℕ)
    (hB : LocallyClosedTreeCompletable Base B.toStructure n)
    (Test : Finset (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hcard : Test.card ≤ n)
    (hTest : (UnitAttach B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (hcopy :
      ∀ z : ↥(↑Test : Set _),
        ∃ x : V,
          z.1 =
            Structure.Attachment.copyEmbedding
              B.toStructure S hS D.toStructure
              (fun _ : PUnit.{v+1} => f.toEmbedding)
              PUnit.unit x) :
    HasTreeCompletion Base
      ((UnitAttach B S hS D f).toStructure.induce
        (↑Test : Set _) hTest) := by
  let e :=
    testEmbeddingToCopy
      (B := B) (S := S) (hS := hS) (D := D) (f := f)
      Test hTest hcopy
  have hPull :
      LocallyClosedTreeCompletable Base
        ((UnitAttach B S hS D f).toStructure.induce
          (↑Test : Set _) hTest) n :=
    hB.pullback_embedding e
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  letI : Fintype ↥TestSet := Fintype.ofFinite _
  have hcard' :
      Fintype.card ↥TestSet ≤ n := by
    simpa [TestSet] using hcard
  exact hPull.fullWitness hcard'

/-- Pure-core local-tree witness for one EHN attachment. -/
theorem pureCore_locallyClosedTreeCompletable
    {VB : Type v} {Base : Structure L VB}
    (n : ℕ)
    (hD : LocallyClosedTreeCompletable Base D.toStructure n)
    (Test : Finset (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})))
    (hcard : Test.card ≤ n)
    (hTest : (UnitAttach B S hS D f).toStructure.IsClosed
      (↑Test : Set _))
    (hcore :
      ∀ z : ↥(↑Test : Set _),
        ∃ w : W,
          z.1 =
            Structure.Attachment.coreEmbedding
              B.toStructure S hS D.toStructure
              (fun _ : PUnit.{v+1} => f.toEmbedding) w) :
    HasTreeCompletion Base
      ((UnitAttach B S hS D f).toStructure.induce
        (↑Test : Set _) hTest) := by
  let e :=
    testEmbeddingToCore
      (B := B) (S := S) (hS := hS) (D := D) (f := f)
      Test hTest hcore
  have hPull :
      LocallyClosedTreeCompletable Base
        ((UnitAttach B S hS D f).toStructure.induce
          (↑Test : Set _) hTest) n :=
    hD.pullback_embedding e
  let TestSet : Set
      (Structure.Attachment.Vertex S (W := W) (I := PUnit.{v+1})) :=
    ↑Test
  letI : Fintype ↥TestSet := Fintype.ofFinite _
  have hcard' :
      Fintype.card ↥TestSet ≤ n := by
    simpa [TestSet] using hcard
  exact hPull.fullWitness hcard'

end StructuralRamsey.FunctionalPartite.Attachment
