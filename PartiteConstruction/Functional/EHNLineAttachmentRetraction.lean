import PartiteConstruction.Functional.PowerCoordinateEHN
import PartiteConstruction.Functional.EHNAttachmentDecompose
import PartiteConstruction.Functional.ProjectedIrreducibleCover

/-!
# EHN retraction of ONE genuine functional Hales–Jewett line attachment

The Hales–Jewett power is a genuine partite system with set-valued,
part-TRANSVERSAL operation images. Every coordinate evaluation is an
EHN map to the original selected-support system (PowerCoordinateEHN).

A Hales–Jewett line W has a parameter coordinate i. At that coordinate,
its FULL line embedding of the old selected support is split by
evaluation: coord_i(lineMap_W(x)) = x.

An actual native one-copy EHN attachment is a full functional free
amalgam of the coordinate power CORE and an entire copied OLD Picture
over the selected support, placed by the full line embedding W.

Consequently the map from the core to Old given by evaluating the
parameter coordinate, and the IDENTITY map of the attached old copy,
are EHN and agree on the full support. The already verified EHN
free-amalgam gluing theorem constructs a GLOBAL EHN retraction
from this ONE mixed attachment to the entire old Picture.

This is a substantive native single-attachment shadow construction,
with genuine set-valued operations, no domain-reflection fiction
and no enlarging exact weak-test vertex sets. It does NOT assert one
simultaneous EHN retraction of an HJ Picture with MANY attachments:
different HJ lines may have disjoint sets of parameter coordinates.
The need to coordinate those individual shadows across many line
attachments is the remaining multi-copy combinatorial question.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- A full functional free amalgam admits a right-side EHN
retraction if its left side has an EHN map into the right side
which fixes the entire common full root.

No extra root domain reflection or global vertex injection is
imposed: the source projection is an original-2019 EHN map. -/
theorem ehn_retract_right
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rLeft : E → F)
    (hR : Left.IsEHNHomomorphismEmbedding Right rLeft)
    (hFix : ∀ d : H, rLeft (sL d) = sR d) :
    ∃ q : C → F,
      Whole.IsEHNHomomorphismEmbedding Right q ∧
      (∀ x : E, q (iL x) = rLeft x) ∧
      (∀ x : F, q (iR x) = x) := by
  obtain ⟨q, hq, hqL, hqR⟩ :=
    hFree.exists_EHN_projection rLeft (fun z : F => z)
      hR (Structure.Embedding.id Right).isEHNHomomorphismEmbedding
      hFix
  exact ⟨q, hq, hqL, hqR⟩

end StructuralRamsey.Structure.IsFreeAmalgam


namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable {A : Structure L P} {B : System L P V}
variable {N : ℕ}

/-- Parameter-coordinate evaluation splits its full HJ line
embedding, and the evaluation map is EHN on all irreducibles.
The latter is stronger than its obvious weak homomorphism law.

This is entirely valid with genuinely multivalued but transversal
function images. -/
theorem line_parameter_coordinate_EHN_retraction
    (hB : B.WeaklyPartiteOver A)
    (W : Line (Letter A B) N)
    (i : Fin N) (hi : W.symbol i = .parameter) :
    (power B N).toStructure.IsEHNHomomorphismEmbedding
      B.toStructure (fun z => z.coord i) ∧
    (∀ x : V,
      ((weak_lineEmbedding hB.1 W) x).coord i = x) := by
  constructor
  · exact coordinateEHN hB W.length_pos i
  · intro x
    change (lineMap W x).coord i = x
    simp [lineMap, hi]

end StructuralRamsey.FunctionalPartite.Induced


namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V U : Type v}

/-- A genuine SINGLE binary attachment of an OLD functional Picture
to its selected-support Hales-Jewett power along a full LINE map
admits an EHN retraction onto the attached old Picture.

The retraction acts as identity on the old copy and as evaluation
at one parameter coordinate on the new core. In particular the
coordinate shadow never identifies distinct outputs of an
irreducible source function fibre incorrectly.

Only the parameter coordinate for this particular line is used.
No common parameter is postulated for different attached lines. -/
theorem lineUnitAttachment_EHN_retraction
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U) (alpha : Structure.Embedding A D)
    (N : ℕ)
    (W : Line (Induced.Letter A
      (B.weakRestrict D hB.1 A alpha)) N)
    (i : Fin N) (hi : W.symbol i = .parameter) :
    let S : Set V := B.support alpha.toFunctionEmbedding
    let hS : B.toStructure.IsClosed S :=
      B.weak_support_closed D hB.1 A alpha
    let R := B.weakRestrict D hB.1 A alpha
    let E := Induced.power R N
    let Core := E.relabel alpha.toFunctionEmbedding
    ∃ f : FunctionalPartite.Embedding (B.induce S hS) Core,
      ∃ q : Structure.Attachment.Vertex S
          (W := Induced.Vertex R N) (I := PUnit.{v+1}) → V,
        (Attachment.UnitAttachD B S hS Core f).toStructure.IsEHNHomomorphismEmbedding
          B.toStructure q ∧
        (∀ c : Induced.Vertex R N,
          q (Attachment.unitCoreEmbedding B S hS Core f c) =
            (c.coord i).1) ∧
        (∀ b : V,
          q (Attachment.unitCopyEmbedding B S hS Core f b) = b) := by
  classical
  dsimp only
  let S : Set V := B.support alpha.toFunctionEmbedding
  let hS : B.toStructure.IsClosed S :=
    B.weak_support_closed D hB.1 A alpha
  let R := B.weakRestrict D hB.1 A alpha
  let E := Induced.power R N
  let Core := E.relabel alpha.toFunctionEmbedding
  have hR : R.WeaklyPartiteOver A :=
    B.weakRestrict_invariant D hB.1 A alpha hB
  let line : FunctionalPartite.Embedding R E :=
    Induced.weak_lineEmbedding hR.1 W
  let f : FunctionalPartite.Embedding (B.induce S hS) Core := {
    toEmbedding := line.toEmbedding
    map_part := by
      intro x
      exact (congrArg alpha (line.map_part x)).trans
        (B.restrictedPart_spec alpha.toFunctionEmbedding x)
  }
  let rCore : Induced.Vertex R N → V :=
    fun z => (z.coord i).1
  have hCoordinate :
      E.toStructure.IsEHNHomomorphismEmbedding
        R.toStructure (fun z => z.coord i) :=
    (Induced.line_parameter_coordinate_EHN_retraction hR W i hi).1
  let inc : Structure.Embedding R.toStructure B.toStructure :=
    B.weakRestrictInclusion D hB.1 A alpha
  have hrCore :
      Core.toStructure.IsEHNHomomorphismEmbedding
        B.toStructure rCore :=
    inc.isEHNHomomorphismEmbedding.comp hCoordinate
  have hFix : ∀ x : S, rCore (f x) = x.1 := by
    intro x
    have hx :=
      (Induced.line_parameter_coordinate_EHN_retraction hR W i hi).2 x
    exact congrArg Subtype.val hx
  have hFree :=
    Attachment.unit_isFreeAmalgam_full B S hS Core f
  obtain ⟨q, hq, hqCore, hqCopy⟩ :=
    hFree.ehn_retract_right rCore hrCore hFix
  exact ⟨f, q, hq, hqCore, hqCopy⟩

end StructuralRamsey.FunctionalPartite.EHN
