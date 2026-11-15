import PartiteConstruction.Functional.TrackAWeakMapActiveCoverPullback2019
import PartiteConstruction.Functional.EHNPartPreservingRetractAppend
import PartiteConstruction.Functional.WeakInvariant

/-!
# Track A — exact active-cover weak roots under genuine EHN retractions

The strong Track A source-side improvement is that active-output-part
cover pulls back along a merely POSITIVE, part-preserving weak
functional map. In particular it is stable under a part-preserving
EHN homomorphism-embedding that need not be a full embedding.

Specialize to the ACTUAL binary native EHN attachment from the
existing part-preserving-retraction theorem. Given the same precise
full root embedding and a core EHN shadow q back to B which fixes
the attaching root pointwise, the existing construction produces one
EHN retraction r of the actual attached Stage onto B. It preserves
the part labels and fixes the newly copied old stage.

For EVERY arbitrary exact weak support T of B satisfying the local
active-output-part criterion, its literal preimage r⁻¹(T) in the
actual attached native System also satisfies active cover. This
uses only positive function-output incidence preservation of r, not
global full-fibre surjectivity or domain reflection.

The retraction's *existence* remains an explicit hypothesis through
q and the root-fixing equation. These are known for appropriate
compatible native Hales–Jewett lines but not automatic for arbitrary
successive unrelated lines. No strict full-functional mixed-root
B-tree target witness or class-local completion is constructed.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- EVERY actual coordinate projection from the genuine native
Hales–Jewett power is a positive weak functional homomorphism
preserving part labels. The inverse image of any arbitrary locally
active-covered weak support in the original system is therefore
active-covered in the literal POWER vertex set. No assumption that
the projection is full, injective, or domain-reflecting. -/
theorem power_coordinate_preimage_activeWeakOutputPartCover
    (B : System L P V) (N : ℕ) (i : Fin N)
    (S : Set V) (hS : B.ActiveWeakOutputPartCover S) :
    (power B N).ActiveWeakOutputPartCover
      ((fun z : Vertex B N => z.coord i) ⁻¹' S) := by
  exact System.ActiveWeakOutputPartCover.preimage_weakHom
    (power B N) B (fun z : Vertex B N => z.coord i)
    (fun z => z.belongs i)
    (coordinateWeak (B := B) i) S hS

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W : Type v}

/-- With a compatible part-preserving EHN core shadow, the ACTUAL
native binary attachment inherits active cover on the exact
preimage of any active-covered weak support of the old copied
System. The witness is the genuine attachment retraction, retaining
its core/copy equations and part labels. -/
theorem unitAttach_activeCover_preimage_of_partPreserving_EHN_retraction
    (B : System L P V)
    (Root : Set V) (hRoot : B.toStructure.IsClosed Root)
    (Core : System L P W)
    (f : FunctionalPartite.Embedding (B.induce Root hRoot) Core)
    (q : W → V)
    (hq : Core.toStructure.IsEHNHomomorphismEmbedding B.toStructure q)
    (hFix : ∀ x : Root, q (f x) = x.1)
    (hPart : ∀ w : W, B.part (q w) = Core.part w)
    (T : Set V)
    (hT : B.ActiveWeakOutputPartCover T) :
    ∃ r : Structure.Attachment.Vertex Root
        (W := W) (I := PUnit.{v+1}) → V,
      (Attachment.UnitAttachD B Root hRoot Core f).toStructure.IsEHNHomomorphismEmbedding
        B.toStructure r ∧
      (∀ w : W,
        r (Attachment.unitCoreEmbedding B Root hRoot Core f w) = q w) ∧
      (∀ b : V,
        r (Attachment.unitCopyEmbedding B Root hRoot Core f b) = b) ∧
      (∀ z : Structure.Attachment.Vertex Root
          (W := W) (I := PUnit.{v+1}),
        B.part (r z) =
          (Attachment.UnitAttachD B Root hRoot Core f).part z) ∧
      (Attachment.UnitAttachD B Root hRoot Core f).ActiveWeakOutputPartCover
        (r ⁻¹' T) := by
  obtain ⟨r, hr, hrCore, hrCopy, hrPart⟩ :=
    unitAttach_extend_partPreserving_EHN_retraction
      B Root hRoot Core f q hq hFix hPart
  refine ⟨r, hr, hrCore, hrCopy, hrPart, ?_⟩
  exact System.ActiveWeakOutputPartCover.preimage_ehn
    (Attachment.UnitAttachD B Root hRoot Core f)
    B r hrPart hr T hT

end StructuralRamsey.FunctionalPartite.EHN
