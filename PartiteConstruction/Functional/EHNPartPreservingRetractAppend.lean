import PartiteConstruction.Functional.EHNLineAttachmentRetraction
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Track D: composable, part-preserving EHN shadows across native attachments

A single actual Hales--Jewett LINE attachment has an EHN retraction to
the copied old stage, proved in EHNLineAttachmentRetraction. To iterate
that argument over a finite Picture history one needs more than a
retraction of the initial core: after every previous attachment the
current shadow must SPLIT the next full selected-support embedding.

This module extracts the exact binary induction step for arbitrary
set-valued functional partite systems. It preserves the original
control part labels, the EHN projection, and strict full-functional
exact-weak-test history witnesses with NO increase in the n-vertex
budget. The new side is a FULL copied old stage; the projection is
only EHN (original-source-defined), never assumed total-fibre-exact.

The hypothesis q(f(x))=x is essential. It holds for a single genuine
HJ line by evaluation at its parameter coordinate, and for a family
sharing a common parameter coordinate. It does NOT hold automatically
for successive lines with different parameter coordinates; indeed the
three-line seven-cycle regression excludes that naive strengthening.
The multi-generated maximal mixed-root completion remains OPEN.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W UA VB : Type v}

/-- Extend an existing part-preserving EHN retraction of the current
Picture onto the old stage through ONE more native full attachment,
provided the shadow fixes the precise attaching support pointwise.

The resulting retraction is the old projection on the retained core,
the identity on the new OLD copy, and commutes with the original
control part map on EVERY vertex. No closure hull is substituted for
the exact attaching support, and all set-valued outputs stay part
transversal by the native attachment construction. -/
theorem unitAttach_extend_partPreserving_EHN_retraction
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (q : W → V)
    (hq : D.toStructure.IsEHNHomomorphismEmbedding B.toStructure q)
    (hFix : ∀ x : S, q (f x) = x.1)
    (hPart : ∀ w : W, B.part (q w) = D.part w) :
    ∃ r : Structure.Attachment.Vertex S
        (W := W) (I := PUnit.{v+1}) → V,
      (Attachment.UnitAttachD B S hS D f).toStructure.IsEHNHomomorphismEmbedding
        B.toStructure r ∧
      (∀ w : W, r (Attachment.unitCoreEmbedding B S hS D f w) = q w) ∧
      (∀ b : V, r (Attachment.unitCopyEmbedding B S hS D f b) = b) ∧
      (∀ z : Structure.Attachment.Vertex S
          (W := W) (I := PUnit.{v+1}),
        B.part (r z) = (Attachment.UnitAttachD B S hS D f).part z) := by
  let C := Attachment.UnitAttachD B S hS D f
  have hFree := Attachment.unit_isFreeAmalgam_full B S hS D f
  obtain ⟨r, hr, hrCore, hrCopy⟩ :=
    hFree.ehn_retract_right q hq hFix
  let fullCore : FunctionalPartite.Embedding D C :=
    Attachment.coreEmbedding B S hS D (fun _ : PUnit.{v+1} => f)
  let fullCopy : FunctionalPartite.Embedding B C :=
    Attachment.copyEmbedding B S hS D
      (fun _ : PUnit.{v+1} => f) PUnit.unit
  refine ⟨r, hr, hrCore, hrCopy, ?_⟩
  intro z
  rcases hFree.covers z with ⟨w, hw⟩ | ⟨b, hb⟩
  · subst z
    calc
      B.part (r (Attachment.unitCoreEmbedding B S hS D f w)) =
          B.part (q w) := congrArg B.part (hrCore w)
      _ = D.part w := hPart w
      _ = C.part (Attachment.unitCoreEmbedding B S hS D f w) :=
        (fullCore.map_part w).symm
  · subst z
    calc
      B.part (r (Attachment.unitCopyEmbedding B S hS D f b)) =
          B.part b := congrArg B.part (hrCopy b)
      _ = C.part (Attachment.unitCopyEmbedding B S hS D f b) :=
        (fullCopy.map_part b).symm

/-- A compatible native binary attachment preserves all n-vertex
strict full-functional weak-history witnesses from the ORIGINAL old
stage, with ambient actual A-copy intersections and arbitrary finite
control histories, without any closure or cardinality inflation.

This theorem discharges the *propagation*, not the still-open
existence of compatible retractions for unrelated HJ lines. -/
theorem unitAttach_preserves_strictWeakHistory_of_retraction
    [DecidableEq V]
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (q : W → V)
    (hq : D.toStructure.IsEHNHomomorphismEmbedding B.toStructure q)
    (hFix : ∀ x : S, q (f x) = x.1)
    (hPart : ∀ w : W, B.part (q w) = D.part w)
    (TestA : Structure L UA) (Base : Structure L VB)
    (hTestA : TestA.Irreducible)
    (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMost
      TestA Base B.toStructure B.part n) :
    SetAmbientRelativeWeakTreeWitness.AtMost
      TestA Base (Attachment.UnitAttachD B S hS D f).toStructure
      (Attachment.UnitAttachD B S hS D f).part n := by
  obtain ⟨r, hr, _hrCore, _hrCopy, hrPart⟩ :=
    unitAttach_extend_partPreserving_EHN_retraction
      B S hS D f q hq hFix hPart
  exact SetAmbientRelativeWeakTreeWitness.AtMost.pullback_ehn_commutingParts
    (Attachment.UnitAttachD B S hS D f).part
    B.part r hr (fun z => (hrPart z).symm)
    hTestA n hOld

end StructuralRamsey.FunctionalPartite.EHN
