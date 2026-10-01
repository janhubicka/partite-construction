import PartiteConstruction.Partite.Induced
import PartiteConstruction.Partite.Initial

/-! # Initial picture for the induced construction

The initial picture is the disjoint union of one copy of `B` for every
embedding of `B` into the base structure `D`. Irreducible substructures
cannot cross between two disjoint copies.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {I : Type z}

/-- The projection of every irreducible substructure of a partite system
extends inside a copy of `B` in `D`. This packages invariant (3) of the
induced partite construction. -/
def CoversIrreduciblesBy {X : Type*} (C : System L P X)
    (B : RelStructure L V) (D : RelStructure L P) : Prop :=
  ∀ (T : Set X), (C.toRelStructure.induce T).Irreducible →
    ∃ β : RelStructure.Embedding B D,
      ∀ z : T, ∃ b : V, C.part z.1 = β b

namespace Initial

variable (B : RelStructure L V) (β : I → V ↪ P)

/-- An irreducible substructure of the disjoint-union initial picture lies in
one indexed copy. The empty/singleton cases are included. -/
theorem irreducible_same_index [Nonempty I]
    (T : Set (I × V))
    (hT : ((Partite.Initial.picture B β).toRelStructure.induce T).Irreducible) :
    ∃ i : I, ∀ z : T, z.1.1 = i := by
  classical
  by_cases hne : T.Nonempty
  · obtain ⟨a, haT⟩ := hne
    let aT : T := ⟨a, haT⟩
    refine ⟨a.1, ?_⟩
    intro b
    by_cases hba : b = aT
    · subst b
      rfl
    · obtain ⟨R, z, k, l, hz, hzk, hzl⟩ := hT hba
      change (Partite.Initial.picture B β).rel R (Subtype.val ∘ z) at hz
      rcases hz with ⟨j, y, hy, heq⟩
      have hbj : b.1.1 = j := by
        have h := congrArg Prod.fst (congrFun heq k)
        simpa only [Function.comp_apply, hzk] using h
      have haj : aT.1.1 = j := by
        have h := congrArg Prod.fst (congrFun heq l)
        simpa only [Function.comp_apply, hzl] using h
      exact hbj.trans haj.symm
  · refine ⟨Classical.choice (inferInstance : Nonempty I), ?_⟩
    intro z
    exact (hne ⟨z.1, z.2⟩).elim

variable {Q : Type*} (D : RelStructure L P)
variable (γ : I → RelStructure.Embedding B D)

/-- A disjoint union of copies whose projections are embeddings into `D`
is a `D`-partite system. -/
theorem picture_isPartiteOver [Nonempty I] :
    (Partite.Initial.picture B (fun i => (γ i).toFunctionEmbedding)).IsPartiteOver D := by
  let C := Partite.Initial.picture B (fun i => (γ i).toFunctionEmbedding)
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    rcases hx with ⟨i, y, hy, rfl⟩
    change D.rel R (γ i ∘ y)
    exact ((γ i).map_rel_iff R y).mpr hy
  · intro T hT
    exact C.part_injOn_irreducible T hT
  · intro T hT R x hxT hD
    obtain ⟨i, hi⟩ :=
      irreducible_same_index B (fun j => (γ j).toFunctionEmbedding) T hT
    let y : Fin (L.arity R) → V := fun k => (x k).2
    have htarget : D.rel R (γ i ∘ y) := by
      convert hD using 1
      funext k
      have hik := hi ⟨x k, hxT k⟩
      change γ i ((x k).2) = γ (x k).1 ((x k).2)
      rw [hik]
    have hB : B.rel R y := ((γ i).map_rel_iff R y).mp htarget
    refine ⟨i, y, hB, ?_⟩
    funext k
    apply Prod.ext
    · exact hi ⟨x k, hxT k⟩
    · rfl

/-- The initial picture satisfies invariant (3): every irreducible
substructure projects into one of the indexed copies of `B` in `D`. -/
theorem picture_covers [Nonempty I] :
    CoversIrreduciblesBy
      (Partite.Initial.picture B (fun i => (γ i).toFunctionEmbedding)) B D := by
  intro T hT
  obtain ⟨i, hi⟩ :=
    irreducible_same_index B (fun j => (γ j).toFunctionEmbedding) T hT
  refine ⟨γ i, ?_⟩
  intro z
  refine ⟨z.1.2, ?_⟩
  change γ z.1.1 z.1.2 = γ i z.1.2
  rw [hi z]

end Initial
end StructuralRamsey.Partite.Induced
