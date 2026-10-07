import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Strong induction for finite EHN projections

A finite source carrying an EHN projection has the same recursive dichotomy
used throughout the functional sparsening argument.  If the source is
irreducible, the EHN condition represents the projection by a genuine full
embedding into the outer structure.  Otherwise the source has a proper free
decomposition, and the restricted projections on both sides are again EHN.

This file packages the cardinal induction once, so later rooted-tree
invariants only need to supply their embedded and free-amalgam branches.
-/

namespace StructuralRamsey.Structure.IsEHNHomomorphismEmbedding

universe u v

variable {L : Language.{u}}
variable {P W : Type v}
variable {D : Structure L P}
variable {C : Structure L W}
variable {p : W → P}

/-- Strong induction on the carrier of a finite EHN source.

The predicate may depend on both the source structure and its projection.
The embedded branch receives a full embedding representing the projection
pointwise.  The free branch receives the two recursively established side
predicates for a proper free decomposition. -/
theorem finite_free_induction
    [Finite W]
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (Q : ∀ {X : Type v}, Structure L X → (X → P) → Prop)
    (hembed :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → P),
        E.IsEHNHomomorphismEmbedding D q →
        (∃ g : Embedding E D, ∀ x, g x = q x) →
        Q E q)
    (hfree :
      ∀ {X : Type v} [Finite X]
        (E : Structure L X) (q : X → P),
        E.IsEHNHomomorphismEmbedding D q →
        ∀ d : ProperFreeDecomposition E,
          Q d.left (q ∘ d.leftIn) →
          Q d.right (q ∘ d.rightIn) →
          Q E q) :
    Q C p := by
  classical
  let aux :
      ∀ n : ℕ, ∀ {X : Type v} [Fintype X]
        (E : Structure L X) (q : X → P),
        Fintype.card X = n →
        E.IsEHNHomomorphismEmbedding D q →
        Q E q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X instX E q hcard hq
        by_cases hIrr : E.Irreducible
        · obtain ⟨g, hg⟩ :=
            hq.2 E hIrr (Embedding.id E)
          exact hembed E q hq ⟨g, fun x => by
            calc
              g x = q ((Embedding.id E) x) := hg x
              _ = q x := rfl⟩
        · have hdec : Nonempty (ProperFreeDecomposition E) := by
            by_contra hn
            exact hIrr
              ((irreducible_iff_noProperFreeDecomposition E).mpr hn)
          rcases hdec with ⟨d⟩
          letI : Finite d.Left :=
            Finite.of_injective d.leftIn d.leftIn.injective
          letI : Finite d.Right :=
            Finite.of_injective d.rightIn d.rightIn.injective
          letI : Fintype d.Left := Fintype.ofFinite d.Left
          letI : Fintype d.Right := Fintype.ofFinite d.Right
          have hleftCard : Fintype.card d.Left < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.leftIn d.leftIn.injective d.leftProper
          have hrightCard : Fintype.card d.Right < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.rightIn d.rightIn.injective d.rightProper
          have hqLeft :
              d.left.IsEHNHomomorphismEmbedding D
                (q ∘ d.leftIn) :=
            hq.comp d.leftIn.isEHNHomomorphismEmbedding
          have hqRight :
              d.right.IsEHNHomomorphismEmbedding D
                (q ∘ d.rightIn) :=
            hq.comp d.rightIn.isEHNHomomorphismEmbedding
          have hLeft : Q d.left (q ∘ d.leftIn) := by
            exact ih (Fintype.card d.Left) hleftCard
              d.left (q ∘ d.leftIn) rfl hqLeft
          have hRight : Q d.right (q ∘ d.rightIn) := by
            exact ih (Fintype.card d.Right) hrightCard
              d.right (q ∘ d.rightIn) rfl hqRight
          exact hfree E q hq d hLeft hRight
  letI : Fintype W := Fintype.ofFinite W
  exact aux (Fintype.card W) C p rfl hp

end StructuralRamsey.Structure.IsEHNHomomorphismEmbedding
