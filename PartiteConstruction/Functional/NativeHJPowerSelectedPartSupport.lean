import PartiteConstruction.Functional.EHNAttachmentDecompose
import PartiteConstruction.Functional.Induced

/-!
# True Hales-Jewett cores use only selected control parts

The arbitrary-stage C5 obstruction attaches an OLD stage to a CORE
containing a vertex in control part 1, while its selected support has
only control parts 0 and 3. That CORE is not a genuine Hales-Jewett
coordinate power of the selected support.

This file isolates the exact geometric restriction for ANY functional
partite system with set-valued functions:

(1) Every vertex in a POSITIVE coordinate power has the SAME part as
    its chosen coordinate, so all power parts come from the original
    selected system.
(2) In a genuine one-copy binary attachment, if every CORE vertex
    has part in selected J, any attached vertex whose part lies
    OUTSIDE J necessarily belongs to the attached OLD copy, not
    the CORE. It has the canonical Sum.inr tag.

The statements need no global total-fibre projection, closure hull,
or stronger assumption that copies of A intersect in a single line.
They are only a geometric source-distribution invariant; they do
NOT provide the missing compatible strict B-tree mixed-root witness.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- A genuine nonzero Hales-Jewett coordinate power introduces no
NEW part labels. Every power vertex has the part of any one of its
actual coordinates. -/
theorem power_part_mem_of_mem
    (B : System L P V) (N : ℕ) (hN : 0 < N)
    (J : Set P) (hPart : ∀ y : V, B.part y ∈ J)
    (x : Vertex B N) :
    (power B N).part x ∈ J := by
  let i : Fin N := ⟨0,hN⟩
  have h : B.part (x.coord i) ∈ J := hPart (x.coord i)
  simpa only [power, x.belongs i] using h

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.Attachment

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- In an actual one-copy native binary EHN attachment, no vertex
in a control part OUTSIDE the CORE part set can be a core vertex.
It must have the original non-support OLD copy constructor tag.

The overlap S need only be function closed, not irreducible. -/
theorem unit_outside_core_parts_is_copy
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (D : System L P W)
    (f : FunctionalPartite.Embedding (B.induce S hS) D)
    (J : Set P)
    (hCore : ∀ y : W, D.part y ∈ J)
    (x : Structure.Attachment.Vertex S (W := W)
      (I := PUnit.{v+1}))
    (hx : (UnitAttachD B S hS D f).part x ∉ J) :
    ∃ (i : PUnit.{v+1}) (y : {y : V // y ∉ S}),
      x = Sum.inr (i,y) := by
  cases x with
  | inl y =>
      have hc : (UnitAttachD B S hS D f).part (Sum.inl y) ∈ J := by
        change D.part y ∈ J
        exact hCore y
      exact (hx hc).elim
  | inr iy =>
      exact ⟨iy.1,iy.2,rfl⟩

/-- Apply the preceding lemma with an ACTUAL nonzero
Hales-Jewett POWER as the attaching core. Its vertices
cannot have any unselected control label. -/
theorem unit_power_outside_selected_parts_is_copy
    (B : System L P V) (S : Set V)
    (hS : B.toStructure.IsClosed S)
    (R : System L P W)
    (N : ℕ) (hN : 0 < N)
    (J : Set P)
    (hR : ∀ y : W, R.part y ∈ J)
    (f : FunctionalPartite.Embedding
      (B.induce S hS) (Induced.power R N))
    (x : Structure.Attachment.Vertex S
      (W := Induced.Vertex R N) (I := PUnit.{v+1}))
    (hx : (UnitAttachD B S hS (Induced.power R N) f).part x ∉ J) :
    ∃ (i : PUnit.{v+1}) (y : {y : V // y ∉ S}),
      x = Sum.inr (i,y) := by
  exact unit_outside_core_parts_is_copy B S hS (Induced.power R N)
    f J (fun y => Induced.power_part_mem_of_mem R N hN J hR y)
    x hx

end StructuralRamsey.FunctionalPartite.Attachment
