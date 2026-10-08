import PartiteConstruction.Functional.EHNPictureWeakTree
import PartiteConstruction.Functional.EHNInitial
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Native functional initial pictures with weak vertex-tree control

The EHN initial Picture consists of genuine full B-copies glued along
the empty support (for positive-arity functions).  Each copy already
has one-copy relational graph-tree witnesses for arbitrary vertex tests.

The generic projected free-attachment lemma therefore preserves the
controlled weak graph-tree invariant through every initial attachment.
The initial stage still represents every full B-placement in D.

No U-closed relational picture, generated-closure budget, or new Ramsey
argument is used.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

noncomputable section

universe u v
variable {L : Language.{u}} {U V P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Every weak vertex test inside one full copy of B has a tree completion
witnessed by B itself, with all ambient A-copies controlled identically. -/
theorem base_weakGraphLocallyTreeLike
    (A : Structure L U) (B : Structure L V) (n : ℕ) :
    RelStructure.LocallyTreeLike A.graph B.graph B.graph n := by
  classical
  intro S _
  let f : ↥(↑S : Set V) → V := Subtype.val
  have hf :
      (B.graph.induce (↑S : Set V)).IsHomomorphismEmbedding B.graph f :=
    (RelStructure.inclusion B.graph (↑S : Set V)).isHomomorphismEmbedding
  refine ⟨V, B.graph,
    RelStructure.TreeAmalgam.copy (RelStructure.Iso.refl B.graph),
    f, hf, ?_⟩
  intro α
  refine ⟨α, ?_⟩
  intro a ha
  exact ⟨a, rfl⟩

/-- The native initial EHN picture preserves the rank-n weak graph-tree
invariant and still represents every specified full B-placement. -/
theorem initialList_weakGraphLocallyTreeLike
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U]
    (B : Structure L V) [Finite V]
    (hmB : K B)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D)
    (xs : List (Structure.Embedding B D))
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph B.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph B.graph
        T.system.toStructure.graph n ∧
      ∃ root : Structure.Embedding B T.system.toStructure,
        ∀ β ∈ xs,
          ∃ j : Structure.Embedding B T.system.toStructure,
            ∀ x, T.system.part (j x) = β x := by
  classical
  induction xs with
  | nil =>
      let T : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := placed B β₀
        isPartite := placed_over B β₀
        mem := hmB
      }
      refine ⟨T, ?_, Structure.Embedding.id B, ?_⟩
      · exact base_weakGraphLocallyTreeLike A B n
      · intro _ h
        exact (List.not_mem_nil h).elim
  | cons β xs ih =>
      obtain ⟨T, hT, root, hcopies⟩ := ih
      let Q := placed B β
      have hS : Q.toStructure.IsClosed ∅ := empty_closed B hpos
      let f : FunctionalPartite.Embedding (Q.induce ∅ hS) T.system := {
        toEmbedding := root.comp (Structure.inclusion B ∅ hS)
        map_part := fun x => x.2.elim
      }
      let QStage : Stage K D := {
        Carrier := V
        finiteCarrier := inferInstance
        system := Q
        isPartite := placed_over B β
        mem := hmB
      }
      let R := T.attach hK Q (placed_over B β) hmB ∅ hS f
      have hSupport : ∀ x : V, x ∈ (∅ : Set V) →
          ∃ a : U, Q.part x = (β₀.comp eAB) a := by
        intro x hx
        exact hx.elim
      have hR :
          RelStructure.LocallyTreeLike A.graph B.graph
            R.system.toStructure.graph n := by
        have hBase :
            RelStructure.LocallyTreeLike A.graph B.graph
              QStage.system.toStructure.graph n :=
          base_weakGraphLocallyTreeLike A B n
        exact T.attach_weakGraphLocallyTreeLike
          hK A B D hA eAB QStage ∅ hS f (β₀.comp eAB)
          hSupport n hn hD hBase hT
      let j : FunctionalPartite.Embedding T.system R.system :=
        FunctionalPartite.Attachment.coreEmbedding
          Q ∅ hS T.system (fun _ : PUnit.{v+1} => f)
      let b : FunctionalPartite.Embedding Q R.system :=
        FunctionalPartite.Attachment.copyEmbedding
          Q ∅ hS T.system (fun _ : PUnit.{v+1} => f) PUnit.unit
      refine ⟨R, hR, j.toEmbedding.comp root, ?_⟩
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ
      · exact ⟨b.toEmbedding, b.map_part⟩
      · obtain ⟨e, he⟩ := hcopies γ hγ
        exact ⟨j.toEmbedding.comp e,
          fun x => (j.map_part (e x)).trans (he x)⟩

/-- A finite genuine functional initial stage simultaneously realizes all
B-placements and controls every weak test on at most n vertices. -/
theorem initial_weakGraphLocallyTreeLike
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U]
    (B : Structure L V) [Finite V] [Finite P]
    (hmB : K B)
    (hA : A.graph.HereditarilyIrreducible)
    (eAB : Structure.Embedding A B)
    (hpos : L.PositiveFuncArity)
    (β₀ : Structure.Embedding B D)
    (n : ℕ) (hn : 0 < n)
    (hD : RelStructure.LocallyTreeLike A.graph B.graph D.graph (n - 1)) :
    ∃ T : Stage K D,
      RelStructure.LocallyTreeLike A.graph B.graph
        T.system.toStructure.graph n ∧
      ∀ β : Structure.Embedding B D,
        ∃ j : Structure.Embedding B T.system.toStructure,
          ∀ x, T.system.part (j x) = β x := by
  classical
  letI : Fintype (Structure.Embedding B D) := Fintype.ofFinite _
  obtain ⟨T, hT, _, hc⟩ :=
    initialList_weakGraphLocallyTreeLike
      hK A B hmB hA eAB hpos β₀ Finset.univ.toList n hn hD
  exact ⟨T, hT, fun β => hc β (by simp)⟩

end

end StructuralRamsey.FunctionalPartite.EHN
