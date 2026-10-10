import PartiteConstruction.Ramsey.ClosurePictureCoordinate
import PartiteConstruction.Ramsey.ClosurePartitePower
import PartiteConstruction.Iterated.AttachmentProjection

/-!
# An ordinary homomorphism-embedding retraction of native line subattachments

The previous CLOSED-test retraction theorem for a native Hales--Jewett
subattachment used the U-closedness of the WHOLE attachment and a
relative U-closed attaching support. Those assumptions are not
appropriate for the temporarily conflicting little Picture of the
unrestricted recursive Ramsey construction.

For purposes of analysing an exact WEAK test, a less restrictive
but genuine map is available:

If coordinate k is a parameter on every line of a chosen subfamily,
evaluate core vertices at k and send every attached OLD copy by the
identity. This defines an ORDINARY relational homomorphism-embedding
from the ACTUAL subattachment into Old, even when its support is
nonclosed and the subattachment itself is not semi-closed.

The proof uses the already verified ordinary HE coordinate map
power(R,N) -> R, followed by the full induced support inclusion
R -> Old. Along each attached line, coordinate k evaluates its
attaching map to the ORIGINAL support vertex. The general
fold_isHomomorphismEmbedding theorem for simultaneous attachments
then yields the map. No U-closure or K-completion oracle occurs.

This may provide the distinct side projections required by the
two-side generated-boundary completion criterion in draft #214,
once actual mixed weak tests are decomposed along their native
line history. There is no assertion that ALL lines in the Ramsey
family share a coordinate, which would be false.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}}
variable {P Q V I : Type v} {N : ℕ}

/-- Every selected native subfamily with a common parameter
coordinate admits an ORDINARY homomorphism-embedding into Old by
evaluating the central core and retaining each old copy unchanged.

In contrast with the older protected retraction, neither the
support S nor the whole attachment is required U-closed or even
U-semi-closed. This is exactly the ordinary map needed for
maximal-U-rank weak tests, whose closed irreducible tests become
ordinary irreducible by merged #211. -/
theorem line_subfamily_coordinate_homomorphismEmbedding
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (k : Fin N)
    (hVariable : ∀ i : I, (lines i).symbol k = .parameter) :
    let R := Old.restrict alpha
    let S := Old.support alpha
    let Core := (power R N).toRelStructure
    let maps := closureLineMaps Old alpha A hRestricted lines
    RelStructure.IsHomomorphismEmbedding
      (RelStructure.Attachment.attach Old.toRelStructure S Core maps)
      Old.toRelStructure
      (RelStructure.Attachment.fold
        (fun z : Vertex R N => (z.coord k).1)
        (fun _ : I => id)) := by
  let R := Old.restrict alpha
  let S := Old.support alpha
  let Core := (power R N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let coreMap : Vertex R N → V := fun z => (z.coord k).1
  let oldCopies : I →
      RelStructure.Embedding Old.toRelStructure Old.toRelStructure :=
    fun _ => RelStructure.Embedding.id Old.toRelStructure
  have hCoreHE : Core.IsHomomorphismEmbedding Old.toRelStructure coreMap :=
    (inclusion Old.toRelStructure S).isHomomorphismEmbedding.comp
      (coordinate_isHomomorphismEmbedding R hRestricted k)
  have hCompat : ∀ i : I, ∀ x : S,
      coreMap (maps i x) = oldCopies i x.1 := by
    intro i x
    change ((NonInduced.lineMap (lines i) x).coord k).1 = x.1
    rw [coordinate_lineMap_parameter (lines i) k (hVariable i) x]
  exact RelStructure.Attachment.fold_isHomomorphismEmbedding
    coreMap oldCopies hCompat hCoreHE

end StructuralRamsey.Partite.Induced
