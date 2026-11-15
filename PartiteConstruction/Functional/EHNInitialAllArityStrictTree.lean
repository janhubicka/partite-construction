import PartiteConstruction.Functional.InitialTreeCompletion

/-!
# Track D: ACTUAL strict initial functional Picture with nullary functions

English proof committed FIRST:
docs/track-d-english-nullary-all-arity-initial-strict-tree-20261114.md

The verified native all-arity initial Picture glues genuine placed
Base-copies over their FULL canonical nullary root, transported
between different full placements. If Base itself is irreducible,
every FULL attaching nullary-root map is contained inside the
distinguished FULL Base-copy on its side. Therefore the SAME
all-arity construction is actually a strict full-functional
TreeAmalgam of Base-copies at every finite stage.

Nullary outputs are NOT discarded, and neither an empty
root nor positivity of function arities is assumed. This
strengthens the initial strict tree base case only; no
unrestricted mixed HJ rank successor is claimed.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The ACTUAL all-arity native finite initial-list construction
is a genuine STRICT full-functional Base-tree whenever Base is
irreducible. Copies of Base are joined over the FULL canonical
nullary root, never over the generally nonclosed empty set.

The distinguished root Base-copy and all required full control
placements survive, exactly as in the already verified
`initialList_allArity` class/arrow construction. -/
theorem initialList_allArity_tree
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V]
    (hmBase : K Base)
    (hBase : Base.Irreducible)
    (beta0 : Structure.Embedding Base D)
    (xs : List (Structure.Embedding Base D)) :
    ∃ T : Stage K D,
      Structure.TreeAmalgam
        Base T.Carrier T.system.toStructure ∧
      ∃ root : Structure.Embedding Base T.system.toStructure,
        (∀ x, T.system.part (root x) = beta0 x) ∧
        ∀ beta ∈ xs,
          ∃ e : Structure.Embedding Base T.system.toStructure,
            ∀ x, T.system.part (e x) = beta x := by
  induction xs with
  | nil =>
      let T : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed Base beta0
        isPartite := placed_over Base beta0
        mem := hmBase
      }
      have hTree : Structure.TreeAmalgam
          Base T.Carrier T.system.toStructure :=
        Structure.TreeAmalgam.copy
          (Structure.Embedding.id Base) (fun x => ⟨x, rfl⟩)
      exact ⟨T, hTree, Structure.Embedding.id Base,
        (fun _ => rfl),
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons beta xs ih =>
      obtain ⟨T, hTreeT, root, hroot, hcopies⟩ := ih
      let Q := placed Base beta
      let S : Set V := Base.nullaryRoot
      have hS : Q.toStructure.IsClosed S :=
        Base.nullaryRoot_isClosed
      let phi := rootTransport Base beta0 beta
      let incRoot : Structure.Embedding
          (Base.induce Base.nullaryRoot Base.nullaryRoot_isClosed)
            Base :=
        Structure.inclusion Base Base.nullaryRoot
          Base.nullaryRoot_isClosed
      let f : FunctionalPartite.Embedding (Q.induce S hS) T.system := {
        toEmbedding := by
          change Structure.Embedding
            (Base.induce Base.nullaryRoot Base.nullaryRoot_isClosed)
            T.system.toStructure
          exact root.comp (incRoot.comp phi)
        map_part := by
          intro x
          calc
            T.system.part (root (incRoot (phi x))) =
                beta0 (phi x).1 := hroot _
            _ = beta x.1 := rootTransport_spec Base beta0 beta x
      }
      let R := T.attach hK Q (placed_over Base beta) hmBase
        S hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding
          Q S hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding
          Q S hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      let rawCore :=
        Structure.Attachment.coreEmbedding
          Q.toStructure S hS T.system.toStructure
          (fun _ : PUnit.{v+1} => f.toEmbedding)
      let rawCopy :=
        Structure.Attachment.copyEmbedding
          Q.toStructure S hS T.system.toStructure
          (fun _ : PUnit.{v+1} => f.toEmbedding) PUnit.unit
      have hFree :
          Structure.IsFreeAmalgam f.toEmbedding incRoot
            rawCore rawCopy := by
        exact Structure.Attachment.unit_isFreeAmalgam
          Q.toStructure S hS T.system.toStructure f.toEmbedding
      have hcT : f.toEmbedding.ContainedInIrreducible := by
        refine ⟨V, Base, hBase, root, ?_⟩
        intro x
        exact ⟨incRoot (phi x), rfl⟩
      have hcBase : incRoot.ContainedInIrreducible := by
        refine ⟨V, Base, hBase, Structure.Embedding.id Base, ?_⟩
        intro x
        exact ⟨incRoot x, rfl⟩
      have hTreeRaw : Structure.TreeAmalgam Base
          (Structure.Attachment.Vertex S
            (W := T.Carrier) (I := PUnit.{v+1}))
          (Structure.Attachment.attach
            Q.toStructure S hS T.system.toStructure
            (fun _ : PUnit.{v+1} => f.toEmbedding)) := by
        exact Structure.TreeAmalgam.glue
          hTreeT
          (Structure.TreeAmalgam.copy
            (Structure.Embedding.id Base) (fun x => ⟨x, rfl⟩))
          f.toEmbedding incRoot hcT hcBase rawCore rawCopy hFree
      have hTreeR :
          Structure.TreeAmalgam Base
            R.Carrier R.system.toStructure := by
        simpa [R, Stage.attach, FunctionalPartite.Attachment.attach,
          rawCore, rawCopy] using hTreeRaw
      refine ⟨R, hTreeR, j.toEmbedding.comp root, ?_, ?_⟩
      · intro x
        exact (j.map_part (root x)).trans (hroot x)
      · intro gamma hgamma
        rcases List.mem_cons.mp hgamma with rfl | hgamma
        · exact ⟨b.toEmbedding, b.map_part⟩
        · obtain ⟨e, he⟩ := hcopies gamma hgamma
          exact ⟨j.toEmbedding.comp e,
            fun x => (j.map_part (e x)).trans (he x)⟩

/-- Enumerate ALL full Base placements into the finite control D.
The SAME original all-arity genuine functional initial Picture
is a STRICT full-functional Base-tree with all required copies.

No `PositiveFuncArity` assumption; canonical nullary roots and
all nullary function outputs are retained. -/
theorem initial_allArity_tree
    (hK : Structure.FreeAmalgamationClass K)
    (Base : Structure L V) [Finite V] [Finite P]
    (hmBase : K Base)
    (hBase : Base.Irreducible)
    (beta0 : Structure.Embedding Base D) :
    ∃ T : Stage K D,
      Structure.TreeAmalgam
        Base T.Carrier T.system.toStructure ∧
      ∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  classical
  letI : Fintype (Structure.Embedding Base D) := Fintype.ofFinite _
  obtain ⟨T, hTree, _, _, hcopies⟩ :=
    initialList_allArity_tree hK Base hmBase hBase
      beta0 Finset.univ.toList
  exact ⟨T, hTree, fun beta => hcopies beta (by simp)⟩

end StructuralRamsey.FunctionalPartite.EHN
