import PartiteConstruction.Functional.TrackBFullCopyWholeMaskUClosure2019
import PartiteConstruction.Functional.TrackBFullClippedWeakTagNaturality2019
import PartiteConstruction.Functional.TrackBExactWeakImageClosure2019
import PartiteConstruction.Functional.NativeFiniteStageUClosedWeakDictionary

/-!
# Track B: one ACTUAL finite functional Picture stage, BOTH 2019 weak tags

The two weak interpretations are different. The original native
functional survey uses CLIPPED weak restriction and output-part-
indexed singleton U-tags; the genuinely partial 2019 convention uses
WHOLE-fibre deletion and complete-mask OLD tags. On arbitrary mixed
multivalued weak tests they have different closure operators and
different generator ranks.

Nevertheless, when a true full functional attached-copy map e:B→T
is restricted to the literal exact preimage of ANY test Test⊆T,
BOTH independently constructed ambient 2019 U-closure operations
are natural along exactly the SAME e and Test: each takes the image
of a generated closure of any seed Q ONTO the closure of the image
seed. This does not equate the two closures to each other.

We package the two theorems with the *same* native Stage.attachList
witness, its original full old-copy maps and core overlap equations,
plus the one-way WHOLE-source-to-CLIPPED-control projection law for
any weak test of the same final T. It is not a relational surrogate
Picture and does not enlarge a tested carrier by its generated hull.

Stage T is in K and has the original EHN weak part projection,
but no global ProjectionHom, full target B-tree completion, intrinsic
H-local completion, or isomorphism of the two OLD tag languages is
asserted.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {P V I : Type v} [Fintype P]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- On exactly the same genuine full copy map, weak target test and
seed, BOTH canonical 2019 UClosureHull presentations preserve closure
IMAGES by equality. This is two independent equalities, NOT equality
of the distinct whole-fibre/clipped closure operators. -/
theorem Stage.fullCopy_both2019UClosureHull_image_eq
    (T : Stage K D)
    (B : System L P V) [Finite V]
    (copy : FunctionalPartite.Embedding B T.system)
    (hPos : L.PositiveFuncArity)
    (Test : Set T.Carrier)
    (Q : Set (copy.toEmbedding.toFun ⁻¹' Test)) :
    let S := copy.toEmbedding.toFun ⁻¹' Test
    let g := restrictMap copy.toEmbedding.toFun Test
    (Structure.imageSet g
      (UClosureHull (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)).induce S) Q) =
     UClosureHull (L.wholeMaskClosureRules P)
       ((wholeMaskTagExpansion
         (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
           T.system.part)).induce Test)
       (Structure.imageSet g Q)) ∧
    (Structure.imageSet g
      (UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q) =
     UClosureHull (L.outputPartIndexed P).patternClosureRules
       ((patternTagExpansion
         (T.system.splitOutputParts).toStructure.patternGraph).induce Test)
       (Structure.imageSet g Q)) := by
  constructor
  · exact T.fullCopy_wholeMaskUClosureHull_image_eq B copy hPos Test Q
  · exact T.fullCopy_outputTaggedUClosureHull_image_eq B copy hPos Test Q

/-- The ORIGINAL full native finite attachList construction supplies
one and the SAME T, core map and all attached B-copy maps with:
  * exact support-overlap equations,
  * BOTH whole-mask and clipped-output tagged UClosureHull image
    equalities along each attached full copy on arbitrary exact Test,
  * WHOLE-source to clipped-control closure IMAGE INCLUSION under the
    stored, merely EHN-weak part projection of the FINAL T.

There is no independent surrogate OLD witness and no simultaneous
canonical-tag isomorphism or strict target-tree conclusion. -/
theorem attachList_both2019UClosureHull_copyAndProjected
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (hPos : L.PositiveFuncArity)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (E : Stage K D)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) E.system)
    (xs : List I) :
    ∃ T : Stage K D,
      ∃ core : FunctionalPartite.Embedding E.system T.system,
        (∀ i ∈ xs,
          ∃ copy : FunctionalPartite.Embedding B T.system,
            (∀ x : S, copy x.1 = core (maps i x)) ∧
            (∀ (Test : Set T.Carrier)
              (Q : Set (copy.toEmbedding.toFun ⁻¹' Test)),
              let S' := copy.toEmbedding.toFun ⁻¹' Test
              let g := restrictMap copy.toEmbedding.toFun Test
              (Structure.imageSet g
                (UClosureHull (L.wholeMaskClosureRules P)
                  ((wholeMaskTagExpansion
                    (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph
                      B.part)).induce S') Q) =
               UClosureHull (L.wholeMaskClosureRules P)
                 ((wholeMaskTagExpansion
                   (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
                     T.system.part)).induce Test)
                 (Structure.imageSet g Q)) ∧
              (Structure.imageSet g
                (UClosureHull (L.outputPartIndexed P).patternClosureRules
                  ((patternTagExpansion
                    (B.splitOutputParts).toStructure.patternGraph).induce S') Q) =
               UClosureHull (L.outputPartIndexed P).patternClosureRules
                 ((patternTagExpansion
                   (T.system.splitOutputParts).toStructure.patternGraph).induce Test)
                 (Structure.imageSet g Q)))) ∧
        (∀ (Test : Set T.Carrier) (Q : Set Test),
          Structure.imageSet (wholeWeakImageMap T.system.part Test)
            (UClosureHull (L.wholeMaskClosureRules P)
              ((wholeMaskTagExpansion
                (T.system.toStructure.toNonemptyPartial.wholeMaskPatternGraph
                  T.system.part)).induce Test) Q) ⊆
          UClosureHull (L.outputPartIndexed P).patternClosureRules
            ((patternTagExpansion
              ((transversal D).splitOutputParts).toStructure.patternGraph).induce
                (Structure.imageSet T.system.part Test))
            (Structure.imageSet (wholeWeakImageMap T.system.part Test) Q)) := by
  classical
  obtain ⟨T, core, hCopies⟩ :=
    attachList hK B hB hmB S hS E maps xs
  refine ⟨T, core, ?_, ?_⟩
  · intro i hi
    obtain ⟨copy, hCopy⟩ := hCopies i hi
    refine ⟨copy, hCopy, ?_⟩
    intro Test Q
    exact T.fullCopy_both2019UClosureHull_image_eq B copy hPos Test Q
  · intro Test Q
    exact T.exactImageWholeMaskUClosureHull_subset_clipped hPos Test Q

end StructuralRamsey.FunctionalPartite.EHN
