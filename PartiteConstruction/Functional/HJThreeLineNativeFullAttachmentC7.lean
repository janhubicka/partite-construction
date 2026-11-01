import PartiteConstruction.Functional.HJThreeLineNativeOldP5
import PartiteConstruction.Functional.EHNAttachmentDecompose

/-!
# Track D: C7 in a REAL full functional native three-copy attachment

The previous module realizes the selected old P5 support as two full
native A-letters and each of the exact HJ lines W0=(b,p),
W1=(p,a), W2=(p,p) as a full partite embedding into the
actual coordinatewise power.

Here we attach THREE entire old P5 copies to that power using
the genuine `FunctionalPartite.Attachment.attach` with index
`Fin 3`. This retains all old exterior vertices and all relations
and set-valued function incidences exactly. Since the language is
function-free, the seven exact cycle vertices form a function-closed
test automatically.

The resulting full native functional partite System cannot be
two-coloured: its true core contains one HJ matching edge, and the
three FULL old P5 copies produce the remaining six edges of C7.
Consequently it has NO graph homomorphism (and hence no EHN
retraction) back to the bipartite old P5.

This is a **real native full attachment obstruction** to naive
multi-line strict tree preservation, not merely a combinatorial
graph skeleton. It is NOT a proof that this exact object arises as
the particular `EHN.attachList` output of the Ramsey Picture proof,
nor that the strong predecessor-rank hypotheses are satisfied.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

/-- Genuine selected HJ power, relabelled onto parts 0 and 1
of the original three-part control. -/
abbrev Core := (Induced.power R 2).relabel label

def maps (i : Fin 3) :
    FunctionalPartite.Embedding
      (oldSystem.induce support support_closed) Core :=
  selectedLine (chosenLine i)

/-- The actual THREE-COPY native functional attachment. -/
noncomputable abbrev Whole :=
  FunctionalPartite.Attachment.attach
    oldSystem support support_closed Core maps

abbrev Vertex := Structure.Attachment.Vertex support
  (W := Induced.Vertex R 2) (I := Fin 3)

noncomputable abbrev core (z : Induced.Vertex R 2) : Vertex :=
  (FunctionalPartite.Attachment.coreEmbedding
    oldSystem support support_closed Core maps) z

noncomputable abbrev copy (i : Fin 3) (x : Fin 5) : Vertex :=
  (FunctionalPartite.Attachment.copyEmbedding
    oldSystem support support_closed Core maps i) x

def Edge (x y : Vertex) : Prop :=
  Whole.toStructure.rel () (fun k : Fin 2 =>
    if k = 0 then x else y)

/-- Every original old-P5 edge survives FULLY in each actual copy. -/
theorem edge_copy (i : Fin 3) (a b : Fin 5)
    (h : oldEdge a b) : Edge (copy i a) (copy i b) := by
  let tup : Fin 2 → Fin 5 := fun k => if k = 0 then a else b
  have hSrc : oldSystem.toStructure.rel () tup := by
    change oldEdge a b
    exact h
  have hEmb :=
    ((FunctionalPartite.Attachment.copyEmbedding
      oldSystem support support_closed Core maps i).toEmbedding.map_rel_iff
        () tup).mpr hSrc
  simpa only [Edge, copy, tup, Function.comp_apply] using hEmb

/-- Every actual HJ core edge survives in the native full attachment. -/
theorem edge_core (a b : Induced.Vertex R 2)
    (h : Core.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then a else b)) : Edge (core a) (core b) := by
  let tup : Fin 2 → Induced.Vertex R 2 :=
    fun k => if k = 0 then a else b
  have hEmb :=
    ((FunctionalPartite.Attachment.coreEmbedding
      oldSystem support support_closed Core maps).toEmbedding.map_rel_iff
        () tup).mpr h
  simpa only [Edge, core, tup, Function.comp_apply] using hEmb

/-- On every selected old support vertex, the native full copy
embedding is IDENTIFIED with its prescribed full HJ core image. -/
theorem copy_support (i : Fin 3) (x : support) :
    copy i x.1 = core (maps i x) :=
  FunctionalPartite.Attachment.copy_extends
    oldSystem support support_closed Core maps i x

/-- Exact supporting images for old a0 and b1 at every chosen line. -/
theorem maps_a0 (i : Fin 3) :
    maps i ⟨0, by decide⟩ =
      Induced.lineMap (chosenLine i) (false, false) := by
  rfl

theorem maps_b1 (i : Fin 3) :
    maps i ⟨3, by decide⟩ =
      Induced.lineMap (chosenLine i) (true, true) := by
  rfl

theorem copy_a0 (i : Fin 3) :
    copy i 0 =
      core (Induced.lineMap (chosenLine i) (false, false)) := by
  calc
    copy i 0 = core (maps i ⟨0, by decide⟩) :=
      copy_support i ⟨0, by decide⟩
    _ = _ := congrArg core (maps_a0 i)

theorem copy_b1 (i : Fin 3) :
    copy i 3 =
      core (Induced.lineMap (chosenLine i) (true, true)) := by
  calc
    copy i 3 = core (maps i ⟨3, by decide⟩) :=
      copy_support i ⟨3, by decide⟩
    _ = _ := congrArg core (maps_b1 i)

/-- True old bridge edges in both orientations, with the exact
boundary images used by the full attaching embeddings. -/
theorem bridge_a0 (i : Fin 3) :
    Edge (copy i 4)
      (core (Induced.lineMap (chosenLine i) (false, false))) := by
  rw [← copy_a0 i]
  exact edge_copy i 4 0 (by decide)

theorem a0_bridge (i : Fin 3) :
    Edge (core (Induced.lineMap (chosenLine i) (false, false)))
      (copy i 4) := by
  rw [← copy_a0 i]
  exact edge_copy i 0 4 (by decide)

theorem bridge_b1 (i : Fin 3) :
    Edge (copy i 4)
      (core (Induced.lineMap (chosenLine i) (true, true))) := by
  rw [← copy_b1 i]
  exact edge_copy i 4 3 (by decide)

theorem b1_bridge (i : Fin 3) :
    Edge (core (Induced.lineMap (chosenLine i) (true, true)))
      (copy i 4) := by
  rw [← copy_b1 i]
  exact edge_copy i 3 4 (by decide)

/-- Literal C7 cycle vertices in the full native attachment. -/
noncomputable def cycle (i : Fin 7) : Vertex :=
  match i with
  | 0 => copy 0 4
  | 1 => core (Induced.lineMap W0 (false, false))
  | 2 => core (Induced.lineMap W1 (true, true))
  | 3 => copy 1 4
  | 4 => core (Induced.lineMap W1 (false, false))
  | 5 => copy 2 4
  | _ => core (Induced.lineMap W2 (true, true))

/-- Every one of the SEVEN edges of the C7 is a true relation
tuple of the actual native attached functional structure. -/
theorem cycle_edge (i : Fin 7) :
    Edge (cycle i)
      (cycle ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩) := by
  fin_cases i
  · exact bridge_a0 0
  · exact edge_core _ _ NativeTwoLetterHJ.native_core_cross_edge
  · exact b1_bridge 1
  · exact bridge_a0 1
  · have heq : Induced.lineMap W1 (false, false) =
        Induced.lineMap W2 (false, false) :=
      NativeTwoLetterHJ.W1_a0.trans NativeTwoLetterHJ.W2_a0.symm
    rw [heq]
    exact a0_bridge 2
  · exact bridge_b1 2
  · have heq : Induced.lineMap W2 (true, true) =
        Induced.lineMap W0 (true, true) :=
      NativeTwoLetterHJ.W2_b1.trans NativeTwoLetterHJ.W0_b1.symm
    rw [heq]
    exact b1_bridge 0

/-- A two-colouring on ANY target would alternate around the seven
real native attachment edges, impossible for an odd closed walk.
No vertex-distinctness or absence-of-chords premise is needed for
this obstruction (those can be independently verified). -/
theorem not_twoColorable :
    ¬ ∃ c : Vertex → Bool,
      ∀ a b : Vertex, Edge a b → c a ≠ c b := by
  rintro ⟨c, hc⟩
  have eq_of_ne_ne {x y z : Bool}
      (hxy : x ≠ y) (hyz : y ≠ z) : x = z := by
    cases x <;> cases y <;> cases z <;> simp_all
  have h01 : c (cycle 0) ≠ c (cycle 1) :=
    hc _ _ (cycle_edge 0)
  have h12 : c (cycle 1) ≠ c (cycle 2) :=
    hc _ _ (cycle_edge 1)
  have h23 : c (cycle 2) ≠ c (cycle 3) :=
    hc _ _ (cycle_edge 2)
  have h34 : c (cycle 3) ≠ c (cycle 4) :=
    hc _ _ (cycle_edge 3)
  have h45 : c (cycle 4) ≠ c (cycle 5) :=
    hc _ _ (cycle_edge 4)
  have h56 : c (cycle 5) ≠ c (cycle 6) :=
    hc _ _ (cycle_edge 5)
  have h60 : c (cycle 6) ≠ c (cycle 0) :=
    hc _ _ (cycle_edge 6)
  have h02 : c (cycle 0) = c (cycle 2) :=
    eq_of_ne_ne h01 h12
  have h24 : c (cycle 2) = c (cycle 4) :=
    eq_of_ne_ne h23 h34
  have h46 : c (cycle 4) = c (cycle 6) :=
    eq_of_ne_ne h45 h56
  exact h60 (h02.trans (h24.trans h46)).symm

/-- Bipartite colouring of the genuine five-vertex old path. -/
def oldColor (x : Fin 5) : Bool :=
  if x = 0 ∨ x = 3 then false else true

theorem oldColor_edge (a b : Fin 5) (h : oldEdge a b) :
    oldColor a ≠ oldColor b := by
  fin_cases a <;> fin_cases b <;> simp_all [oldColor, oldEdge]

/-- There is NO graph homomorphism from the complete actual native
three-copy attachment to the original P5. Hence no global EHN
shadow/retraction can be constructed across all three lines. -/
theorem no_graph_hom_to_old :
    ¬ ∃ f : Vertex → Fin 5,
      ∀ a b : Vertex, Edge a b → oldEdge (f a) (f b) := by
  rintro ⟨f, hf⟩
  apply not_twoColorable
  refine ⟨oldColor ∘ f, ?_⟩
  intro a b h
  exact oldColor_edge (f a) (f b) (hf a b h)

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7
