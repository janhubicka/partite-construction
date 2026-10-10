import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Iterated.AttachmentProjection

/-!
# The common boundary of an actual native attachment cut lies in its core

An exact weak subset of an attachment can be split into the part
lying in one attached old-picture copy, and the rest (which excludes
only that copy's private exterior vertices). The verified
Attachment.decompose theorem gives a genuine free source amalgam
over the overlap of those two exact sets.

Here we prove directly from the ACTUAL constructors of Attachment:

* Every vertex in that overlap belongs to the central core, even
  when the old support is not U-closed, the core is not U-closed,
  and the whole attachment has conflicting closure outputs.
* Consequently, for any folded projection whose core component
  lands in a selected set J of target vertices, the WHOLE
  separator of the exact weak cut projects into J.

This is the projected-boundary containment hypothesis needed for
small-side completion over the closed hull of one selected A-copy;
unlike the generator-budget condition, it is automatic from the
literal native attachment geometry. It is not an assumption about
a generic abstract free amalgam.

The common boundary may itself be nonclosed and/or reducible.
No completion in K, global semi-closedness, or rank increment is
asserted merely from this geometry.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {V W I P : Type v}
variable (Old : RelStructure L V) (S : Set V)
variable (Core : RelStructure L W)
variable (maps : I → Embedding (Old.induce S) Core)

/-- The exact intersection of a selected attached copy and the rest
contains NO exterior vertex of that copy. It therefore lies wholly
in the genuine central core. This needs no relational closure
hypothesis, nor even partite maps or positivity. -/
theorem overlap_vertex_is_core
    (T : Set (Vertex S (W := W) (I := I))) (i : I)
    (z : OverlapV Old S Core maps T i) :
    ∃ w : W, (z.1.1 : Vertex S (W := W) (I := I)) = Sum.inl w := by
  obtain ⟨x, hx⟩ := z.2.1
  by_cases hxS : x ∈ S
  · refine ⟨maps i ⟨x, hxS⟩, ?_⟩
    exact hx.trans (copyMap_mem i x hxS)
  · have hOut : OutsideAt (W := W) (I := I) S i z.1.1 := by
      refine ⟨⟨x, hxS⟩, ?_⟩
      exact hx.trans (copyMap_not_mem i x hxS)
    exact False.elim (z.2.2 hOut)

/-- A folded map from the native attachment sends its literal
selected-copy/rest overlap wholly into the set J whenever the
CORE map lands in J. The old-copy maps need not be compatible on
the support for this containment assertion: the overlap vertices
are already central-core vertices. -/
theorem overlap_fold_in_selected
    (T : Set (Vertex S (W := W) (I := I))) (i : I)
    (pCore : W → P) (pOld : V → P) (J : Set P)
    (hCore : ∀ w : W, pCore w ∈ J)
    (z : OverlapV Old S Core maps T i) :
    fold pCore (fun _ : I => pOld) z.1.1 ∈ J := by
  obtain ⟨w, hw⟩ := overlap_vertex_is_core Old S Core maps T i z
  rw [hw]
  exact hCore w

end StructuralRamsey.RelStructure.Attachment
