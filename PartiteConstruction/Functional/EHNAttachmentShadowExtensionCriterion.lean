import PartiteConstruction.Functional.EHNAttachmentDecompose
import PartiteConstruction.Functional.ProjectedIrreducibleCover
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# The precise native functional EHN shadow-extension criterion

In a genuine one-copy EHN binary Picture attachment, the core and
the copied old Picture are freely amalgamated over a FULL embedded,
function-closed support S, even though LOCAL bounded tests in the
iterated proof are arbitrary WEAK vertex restrictions.

Suppose the core has an EHN shadow into the old Picture, and suppose
the copied old Picture admits an EHN self-map which agrees with that
shadow on the attaching support. Then the two shadows glue to an EHN
shadow of the ACTUAL entire binary attachment into Old. If both
component shadows preserve their original part labels, so does
their amalgam. Every function-output fibre in the attached partite
system remains TRANSVERSAL.

For the HJ line at a parameter coordinate, the copy's self-map
may be the ID: this is the previously proved one-line retraction.
For a line whose chosen coordinate is a CONSTANT letter e, the
required self-map must extend the partial map
  x ∈ selected support ↦ e(part_A(x))
to the ENTIRE copied old Picture, while commuting with its control
part projection and remaining EHN.

That latter extension is NOT automatic in a free-amalgamation class.
This lemma isolates the exact obstruction to selecting one global
coordinate shadow across all HJ lines without assuming a false
unrestricted root-extension principle.

The source and target remain genuine set-valued FUNCTION structures.
There is no singleton-output reduction, no reflection of undefined
domains, and no closure enlargement of an exact weak local test.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Componentwise EHN maps agreeing on the original full attaching
support glue into one EHN projection of the actual native functional
binary attachment.

The map's restrictions to the full core and copied Old are exactly
the prescribed maps; no source weak substructure is closed or enlarged
as a consequence. -/
theorem unitAttachment_EHN_shadow_of_compatible
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (rCore : W → V) (rCopy : V → V)
    (hCore : D.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure rCore)
    (hCopy : B.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure rCopy)
    (hAgree : ∀ x : S, rCore (f x) = rCopy x.1) :
    ∃ q : Structure.Attachment.Vertex S
        (W := W) (I := PUnit.{v+1}) → V,
      (UnitAttachD B S hS D f).toStructure.IsEHNHomomorphismEmbedding
        B.toStructure q ∧
      (∀ x : W, q (unitCoreEmbedding B S hS D f x) = rCore x) ∧
      (∀ x : V, q (unitCopyEmbedding B S hS D f x) = rCopy x) := by
  exact (unit_isFreeAmalgam_full B S hS D f).exists_EHN_projection
    rCore rCopy hCore hCopy hAgree

/-- If the core and copied-side EHN shadows commute with the
control parts, then their glued map commutes with the control parts
on the WHOLE native attachment. Every set-valued function value set
is part-transversal, as required by the functional partite system. -/
theorem unitAttachment_EHN_shadow_partCompatible
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (rCore : W → V) (rCopy : V → V)
    (hCore : D.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure rCore)
    (hCopy : B.toStructure.IsEHNHomomorphismEmbedding
      B.toStructure rCopy)
    (hAgree : ∀ x : S, rCore (f x) = rCopy x.1)
    (hPartCore : ∀ x : W, B.part (rCore x) = D.part x)
    (hPartCopy : ∀ x : V, B.part (rCopy x) = B.part x) :
    ∃ q : Structure.Attachment.Vertex S
        (W := W) (I := PUnit.{v+1}) → V,
      (UnitAttachD B S hS D f).toStructure.IsEHNHomomorphismEmbedding
        B.toStructure q ∧
      (∀ x : W, q (unitCoreEmbedding B S hS D f x) = rCore x) ∧
      (∀ x : V, q (unitCopyEmbedding B S hS D f x) = rCopy x) ∧
      (∀ z, B.part (q z) = (UnitAttachD B S hS D f).part z) ∧
      (∀ F (x : Fin (L.funcArity F) →
          Structure.Attachment.Vertex S
            (W := W) (I := PUnit.{v+1})),
        Set.InjOn (UnitAttachD B S hS D f).part
          ((UnitAttachD B S hS D f).func F x)) := by
  classical
  let T := UnitAttachD B S hS D f
  obtain ⟨q, hq, hqCore, hqCopy⟩ :=
    unitAttachment_EHN_shadow_of_compatible
      B S hS D f rCore rCopy hCore hCopy hAgree
  have hPart : ∀ z : Structure.Attachment.Vertex S
      (W := W) (I := PUnit.{v+1}),
      B.part (q z) = T.part z := by
    intro z
    rcases (unit_isFreeAmalgam_full B S hS D f).covers z with
        ⟨x, hx⟩ | ⟨y, hy⟩
    · subst z
      calc
        B.part (q (unitCoreEmbedding B S hS D f x)) =
            B.part (rCore x) := congrArg B.part (hqCore x)
        _ = D.part x := hPartCore x
        _ = T.part (unitCoreEmbedding B S hS D f x) :=
          ((coreEmbedding B S hS D
              (fun _ : PUnit.{v+1} => f)).map_part x).symm
    · subst z
      calc
        B.part (q (unitCopyEmbedding B S hS D f y)) =
            B.part (rCopy y) := congrArg B.part (hqCopy y)
        _ = B.part y := hPartCopy y
        _ = T.part (unitCopyEmbedding B S hS D f y) :=
          ((copyEmbedding B S hS D
              (fun _ : PUnit.{v+1} => f) PUnit.unit).map_part y).symm
  refine ⟨q, hq, hqCore, hqCopy, hPart, ?_⟩
  intro F x
  exact T.func_part_injOn F x

end StructuralRamsey.FunctionalPartite.Attachment
