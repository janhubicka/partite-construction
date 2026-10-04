import PartiteConstruction.Iterated.TreeCompletion
import PartiteConstruction.Iterated.ProjectedPartialLocalTreeLike
import PartiteConstruction.Iterated.TraceSelector

/-! # Restoring projected-partial coherence from a larger completion bound

Projected-partial coherence at level n can be recovered from ordinary local
tree completability at a uniformly larger level.

Given an n-vertex test S, record for every copy beta : A -> C the labelled
trace
  a |-> some(beta a) if beta a is in S, and none otherwise.
There are at most (|S|+1)^|A| traces.  Choose one representative beta for
each realized trace and enlarge S by the whole images of those representative
A-copies.

A homomorphism-embedding completion of this enlarged set is induced on every
representative full A-copy because A is irreducible.  Any projected partial
boundary in S has the same labelled trace as one representative, hence agrees
pointwise with that representative on the boundary.  Restricting the target
A-copy supplies the required coherent embedded partial intersection.

The enlargement bound is independent of the size of C.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {C : RelStructure L W}

/-- Uniform size needed to restore projected-partial coherence on n vertices. -/
def projectedPartialRestorationBudget [Fintype U] (n : ℕ) : ℕ :=
  n + (n + 1) ^ Fintype.card U * Fintype.card U

namespace LocallyTreeCompletable

/-- Ordinary local tree completability at the uniform restoration budget
implies projected-partial coherence for the identity projection. -/
theorem toProjectedPartial_identity
    [Fintype U] [Fintype W]
    (hA : A.Irreducible)
    (n : ℕ)
    (hC : LocallyTreeCompletable B C
      (projectedPartialRestorationBudget (U := U) n)) :
    ProjectedPartialLocallyTreeLike
      (A := A) (D := C) (C := C) B id n := by
  classical
  intro S hS

  let Test := ↥(↑S : Set W)
  let Copies := Embedding A C
  letI : Fintype Copies := Fintype.ofFinite _
  let trace : Copies → U → Option Test := fun beta a =>
    if ha : beta a ∈ S then some ⟨beta a, ha⟩ else none

  obtain ⟨J, _hEmpty, hJcard, hrep⟩ :=
    StructuralRamsey.FiniteTrace.selectIndices
      (A := U) (I := Copies) (T := Test) (X := Copies)
      id trace ∅

  let pairs : Finset (Copies × U) := J ×ˢ Finset.univ
  let added : Finset W := pairs.image (fun z => z.1 z.2)
  let R : Finset W := S ∪ added

  have hAddedCard :
      added.card ≤ J.card * Fintype.card U := by
    calc
      added.card ≤ pairs.card := Finset.card_image_le
      _ = J.card * (Finset.univ : Finset U).card := by
        simp [pairs]
      _ = J.card * Fintype.card U := by simp

  have hRcard :
      R.card ≤ projectedPartialRestorationBudget (U := U) n := by
    calc
      R.card ≤ S.card + added.card := Finset.card_union_le _ _
      _ ≤ S.card + J.card * Fintype.card U :=
        Nat.add_le_add_left hAddedCard S.card
      _ ≤ n + ((S.card + 1) ^ Fintype.card U) * Fintype.card U := by
        apply Nat.add_le_add hS
        exact Nat.mul_le_mul_right _ hJcard
      _ ≤ n + ((n + 1) ^ Fintype.card U) * Fintype.card U := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) _
      _ = projectedPartialRestorationBudget (U := U) n := rfl

  obtain ⟨Y, T, hTree, g, hg⟩ := hC R hRcard

  have hSsubR : ∀ w, w ∈ S → w ∈ R := by
    intro w hw
    exact Finset.mem_union_left _ hw

  let eSR : Embedding (C.induce (↑S : Set W)) (C.induce (↑R : Set W)) := {
    toFun := fun x => ⟨x.1, hSsubR x.1 x.2⟩
    injective := by
      intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let f : Test → Y := g ∘ eSR
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f :=
    hg.comp eSR.isHomomorphismEmbedding

  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro beta H e heproj heRange

  obtain ⟨betaRep, hbetaRepJ, htrace⟩ := hrep beta
  have hbetaRepJ' : betaRep ∈ J := by
    simpa using hbetaRepJ

  have hRepR (a : U) : betaRep a ∈ R := by
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(betaRep, a), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hbetaRepJ', Finset.mem_univ a⟩

  let betaR : Embedding A (C.induce (↑R : Set W)) := {
    toFun := fun a => ⟨betaRep a, hRepR a⟩
    injective := by
      intro a b hab
      apply betaRep.injective
      exact congrArg Subtype.val hab
    map_rel_iff := by
      intro Rel x
      change C.rel Rel (betaRep ∘ x) ↔ A.rel Rel x
      exact betaRep.map_rel_iff Rel x
  }

  obtain ⟨betaT, hbetaT⟩ :=
    hg.after_irreducible_embedding hA betaR

  have hRepEq (x : ↥H) : betaRep x.1 = beta x.1 := by
    have hbetaS : beta x.1 ∈ S := by
      have hx := heRange x
      have hp := heproj x
      change e x = beta x.1 at hp
      rw [← hp]
      exact hx
    have ht := congrFun htrace x.1
    by_cases hrepS : betaRep x.1 ∈ S
    · simp only [trace, dif_pos hrepS, dif_pos hbetaS] at ht
      have hs := Option.some.inj ht
      exact congrArg Subtype.val hs
    · simp only [trace, dif_neg hrepS, dif_pos hbetaS] at ht

  let eHT : Embedding (A.induce H) T :=
    betaT.comp (inclusion A H)

  have heHT :
      ∀ x : ↥H, eHT x = f ⟨e x, heRange x⟩ := by
    intro x
    have hp := heproj x
    change e x = beta x.1 at hp
    change betaT x.1 = g (eSR ⟨e x, heRange x⟩)
    rw [hbetaT x.1]
    apply congrArg g
    apply Subtype.ext
    change betaRep x.1 = e x
    rw [hRepEq x, ← hp]

  have hcHT : eHT.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA betaT eHT
    intro x
    exact ⟨x.1, rfl⟩

  exact ⟨eHT, heHT, hcHT⟩

end LocallyTreeCompletable
end StructuralRamsey.RelStructure
