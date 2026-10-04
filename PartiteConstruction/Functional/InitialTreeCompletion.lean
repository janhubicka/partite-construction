import PartiteConstruction.Functional.EHNInitial
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Functional.WeakAttachment

/-! # Functional initial pictures are genuine tree amalgams

For positive-arity functions the EHN initial construction adds each placement
of B by a genuine full free amalgam over the empty closed substructure.  If B
is irreducible, this is exactly a tree-amalgam construction.  This gives the
base case for closed local tree completions without folding different copies
of B onto one another.
-/

namespace StructuralRamsey.Structure.TreeAmalgam

universe u v
variable {L : Language.{u}} {V W : Type v}
variable {Base : Structure L V} {T : Structure L W}

/-- Every genuine functional tree amalgam contains a full embedded copy of
its base. -/
theorem exists_base_embedding
    (hT : TreeAmalgam Base W T) :
    Nonempty (Embedding Base T) := by
  induction hT with
  | copy e _ =>
      exact ⟨e⟩
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      rcases ih₁ with ⟨e⟩
      exact ⟨i₁.comp e⟩

end StructuralRamsey.Structure.TreeAmalgam

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- The positive-arity EHN initial-list construction can be chosen so that its
underlying full structure is itself a genuine tree amalgam of B-copies. -/
theorem initialList_tree
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V]
    (hmB : K B)
    (hBirr : B.Irreducible)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D)
    (xs : List (Structure.Embedding B D)) :
    ∃ T : Stage K D,
      Structure.TreeAmalgam B T.Carrier T.system.toStructure ∧
      ∃ root : Structure.Embedding B T.system.toStructure,
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
      have hTree :
          Structure.TreeAmalgam B V T.system.toStructure := by
        exact Structure.TreeAmalgam.copy
          (Structure.Embedding.id B) (by
            intro x
            exact ⟨x, rfl⟩)
      exact ⟨T, hTree, Structure.Embedding.id B,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons β xs ih =>
      obtain ⟨T, hTreeT, root, hcopies⟩ := ih
      let Q := placed B β
      have hS : Q.toStructure.IsClosed ∅ := empty_closed B hpos
      let inc : Structure.Embedding
          (Q.toStructure.induce ∅ hS) Q.toStructure :=
        Structure.inclusion Q.toStructure ∅ hS
      let f : FunctionalPartite.Embedding (Q.induce ∅ hS) T.system := {
        toEmbedding := root.comp inc
        map_part := fun x => x.2.elim
      }
      let R := T.attach hK Q (placed_over B β) hmB ∅ hS f
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding
          Q ∅ hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding
          Q ∅ hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      have hfree :
          Structure.IsFreeAmalgam f.toEmbedding inc
            j.toEmbedding b.toEmbedding := by
        simpa [j, b] using
          (Structure.Attachment.unit_isFreeAmalgam
            Q.toStructure ∅ hS T.system.toStructure f.toEmbedding)
      obtain ⟨baseInT⟩ := hTreeT.exists_base_embedding
      have hcT : f.toEmbedding.ContainedInIrreducible := by
        refine ⟨V, B, hBirr, baseInT, ?_⟩
        intro x
        exact x.2.elim
      have hcB : inc.ContainedInIrreducible := by
        refine ⟨V, B, hBirr, Structure.Embedding.id B, ?_⟩
        intro x
        exact x.2.elim
      have hTreeR :
          Structure.TreeAmalgam B R.Carrier R.system.toStructure := by
        exact Structure.TreeAmalgam.glue
          hTreeT
          (Structure.TreeAmalgam.copy
            (Structure.Embedding.id B) (by
              intro x
              exact ⟨x, rfl⟩))
          f.toEmbedding inc hcT hcB
          j.toEmbedding b.toEmbedding hfree
      refine ⟨R, hTreeR, j.toEmbedding.comp root, ?_⟩
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hcopies γ hγ
        exact ⟨j.toEmbedding.comp e,
          fun x => (j.map_part (e x)).trans (he x)⟩

/-- Finite positive-arity initial construction with its tree-amalgam
certificate. -/
theorem initial_tree
    (hK : Structure.FreeAmalgamationClass K)
    (B : Structure L V) [Finite V] [Finite P]
    (hmB : K B)
    (hBirr : B.Irreducible)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D) :
    ∃ T : Stage K D,
      Structure.TreeAmalgam B T.Carrier T.system.toStructure ∧
      ∀ β : Structure.Embedding B D,
        ∃ e : Structure.Embedding B T.system.toStructure,
          ∀ x, T.system.part (e x) = β x := by
  classical
  letI : Fintype (Structure.Embedding B D) := Fintype.ofFinite _
  obtain ⟨T, hTree, _, hc⟩ :=
    initialList_tree hK B hmB hBirr hpos β₀ Finset.univ.toList
  exact ⟨T, hTree, fun β => hc β (by simp)⟩

end StructuralRamsey.FunctionalPartite.EHN
