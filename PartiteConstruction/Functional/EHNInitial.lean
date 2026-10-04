import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.Closed

set_option autoImplicit false

/-! # Initial pictures for the functional EHN refinement

The empty overlap is closed for positive-arity functions. Starting with one
B-copy also keeps nullary relation values consistent; no membership of an
arbitrary empty structure is assumed.
-/
namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- Put the vertices of B into the parts prescribed by beta. -/
def placed (B : Structure L V) (β : Structure.Embedding B D) : System L P V where
  toStructure := B
  part := β
  relTransversal := fun _ _ _ _ _ h => β.injective h
  funcTransversal := fun _ _ _ _ _ _ h => β.injective h

theorem placed_over (B : Structure L V) (β : Structure.Embedding B D) :
    (placed B β).WeaklyPartiteOver D := β.isEHNHomomorphismEmbedding

theorem empty_closed (B : Structure L V) (hpos : L.PositiveFuncArity) :
    B.IsClosed ∅ := by
  intro F x hx y hy
  exact (hx ⟨0, hpos F⟩).elim

/-- Initial picture for a finite list of B-placements. The extra root copy
serves only to match nullary relational data at the empty overlaps. -/
theorem initialList
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V]
    (hmB : K B) (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D) (xs : List (Structure.Embedding B D)) :
    ∃ T : Stage K D, ∃ root : Structure.Embedding B T.system.toStructure,
      ∀ β ∈ xs, ∃ e : Structure.Embedding B T.system.toStructure,
        ∀ x, T.system.part (e x) = β x := by
  induction xs with
  | nil =>
      let T : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed B β₀
        isPartite := placed_over B β₀
        mem := hmB
      }
      exact ⟨T, Structure.Embedding.id B, fun _ h => (List.not_mem_nil h).elim⟩
  | cons β xs ih =>
      obtain ⟨T, root, hcopies⟩ := ih
      let Q := placed B β
      have hS : Q.toStructure.IsClosed ∅ := empty_closed B hpos
      let f : FunctionalPartite.Embedding (Q.induce ∅ hS) T.system := {
        toEmbedding := root.comp (Structure.inclusion B ∅ hS)
        map_part := fun x => x.2.elim
      }
      let R := T.attach hK Q (placed_over B β) hmB ∅ hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding Q ∅ hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding Q ∅ hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, j.toEmbedding.comp root, ?_⟩
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hcopies γ hγ
        exact ⟨j.toEmbedding.comp e, fun x => (j.map_part (e x)).trans (he x)⟩

/-- Every full B-embedding into D is represented by a closed copy in the
finite initial picture. -/
theorem initial
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V] [Finite P]
    (hmB : K B) (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D) :
    ∃ T : Stage K D,
      ∀ β : Structure.Embedding B D,
        ∃ e : Structure.Embedding B T.system.toStructure,
          ∀ x, T.system.part (e x) = β x := by
  classical
  letI : Fintype (Structure.Embedding B D) := Fintype.ofFinite _
  obtain ⟨T, _, hc⟩ := initialList hK B hmB hpos β₀ Finset.univ.toList
  exact ⟨T, fun β => hc β (by simp)⟩

/-- Transport the canonical nullary root between two full placements of B in
the same target. Full embeddings map the canonical root onto the target root,
so the two placements differ there only by a full root automorphism. -/
noncomputable def rootTransport
    (B : Structure L V) (β₀ β : Structure.Embedding B D) :
    Structure.Embedding
      (B.induce B.nullaryRoot B.nullaryRoot_isClosed)
      (B.induce B.nullaryRoot B.nullaryRoot_isClosed) := by
  let R := B.induce B.nullaryRoot B.nullaryRoot_isClosed
  let inc : Structure.Embedding R B :=
    Structure.inclusion B B.nullaryRoot B.nullaryRoot_isClosed
  let e : Structure.Embedding R D := β.comp inc
  let j : Structure.Embedding R D := β₀.comp inc
  apply e.factorThroughClosedRange j
  intro x
  have hxD : β x.1 ∈ D.nullaryRoot := by
    have hximg : β x.1 ∈ Structure.imageSet β B.nullaryRoot :=
      ⟨x.1, x.2, rfl⟩
    rw [β.image_nullaryRoot] at hximg
    exact hximg
  obtain ⟨y, hyroot, hy⟩ := β₀.nullaryRoot_surjective (β x.1) hxD
  exact ⟨⟨y, hyroot⟩, hy.symm⟩

theorem rootTransport_spec
    (B : Structure L V) (β₀ β : Structure.Embedding B D)
    (x : B.nullaryRoot) :
    β₀ ((rootTransport B β₀ β x).1) = β x.1 := by
  let R := B.induce B.nullaryRoot B.nullaryRoot_isClosed
  let inc : Structure.Embedding R B :=
    Structure.inclusion B B.nullaryRoot B.nullaryRoot_isClosed
  let e : Structure.Embedding R D := β.comp inc
  let j : Structure.Embedding R D := β₀.comp inc
  change j (rootTransport B β₀ β x) = e x
  rfl

/-- Initial picture for arbitrary function arities. Copies are amalgamated
over the canonical nullary root instead of over the empty structure. -/
theorem initialList_allArity
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V]
    (hmB : K B)
    (β₀ : Structure.Embedding B D) (xs : List (Structure.Embedding B D)) :
    ∃ T : Stage K D, ∃ root : Structure.Embedding B T.system.toStructure,
      (∀ x, T.system.part (root x) = β₀ x) ∧
      ∀ β ∈ xs, ∃ e : Structure.Embedding B T.system.toStructure,
        ∀ x, T.system.part (e x) = β x := by
  induction xs with
  | nil =>
      let T : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed B β₀
        isPartite := placed_over B β₀
        mem := hmB
      }
      exact ⟨T, Structure.Embedding.id B, (fun _ => rfl),
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons β xs ih =>
      obtain ⟨T, root, hroot, hcopies⟩ := ih
      let Q := placed B β
      let S : Set V := B.nullaryRoot
      have hS : Q.toStructure.IsClosed S := B.nullaryRoot_isClosed
      let φ := rootTransport B β₀ β
      let f : FunctionalPartite.Embedding (Q.induce S hS) T.system := {
        toEmbedding := root.comp φ
        map_part := by
          intro x
          calc
            T.system.part (root (φ x)) = β₀ (φ x).1 := hroot _
            _ = β x.1 := rootTransport_spec B β₀ β x
      }
      let R := T.attach hK Q (placed_over B β) hmB S hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding Q S hS T.system
          (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding Q S hS T.system
          (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, j.toEmbedding.comp root, ?_, ?_⟩
      · intro x
        exact (j.map_part (root x)).trans (hroot x)
      · intro γ hγ
        rcases List.mem_cons.mp hγ with rfl | hγ
        · exact ⟨b.toEmbedding, b.map_part⟩
        · obtain ⟨e, he⟩ := hcopies γ hγ
          exact ⟨j.toEmbedding.comp e,
            fun x => (j.map_part (e x)).trans (he x)⟩

/-- Every full B-placement is represented in an initial picture, with no
restriction on function arities. -/
theorem initial_allArity
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V] [Finite P]
    (hmB : K B)
    (β₀ : Structure.Embedding B D) :
    ∃ T : Stage K D,
      ∀ β : Structure.Embedding B D,
        ∃ e : Structure.Embedding B T.system.toStructure,
          ∀ x, T.system.part (e x) = β x := by
  classical
  letI : Fintype (Structure.Embedding B D) := Fintype.ofFinite _
  obtain ⟨T, _, _, hc⟩ :=
    initialList_allArity hK B hmB β₀ Finset.univ.toList
  exact ⟨T, fun β => hc β (by simp)⟩

end StructuralRamsey.FunctionalPartite.EHN
