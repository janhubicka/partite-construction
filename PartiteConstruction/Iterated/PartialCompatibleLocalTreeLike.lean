import PartiteConstruction.Iterated.ControlCompletionCompatible
import PartiteConstruction.Partite.InducedPicture

/-! # Compatibility with partial A-substructures

For the pure-copy branch, controlling intersections with full ambient A-copies
is not enough: a future A-copy may meet the chosen old copy in a proper
substructure that does not extend to an A-copy inside the old stage.

The natural relative invariant is therefore compatibility with every induced
partial substructure of A whose image is contained in the tested set.
This data immediately implies the existing EmbeddedIntersections interface for
full ambient A-copies.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W Y X : Type v}
variable {A : RelStructure L U} {C : RelStructure L W}
variable {T : RelStructure L Y}

/-- Every induced partial A-copy contained in the test is embedded coherently
in the target, with image contained in an irreducible target piece. -/
def PartialEmbeddedIntersections
    (S : Finset W) (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ (H : Set U) (e : Embedding (A.induce H) C)
    (hRange : ∀ x, e x ∈ S),
    ∃ eHT : Embedding (A.induce H) T,
      (∀ x, eHT x = f ⟨e x, hRange x⟩) ∧
      eHT.ContainedInIrreducible

namespace PartialEmbeddedIntersections

/-- Partial compatibility implies the full ambient-copy intersection data used
by compatible control completion. -/
theorem toEmbeddedIntersections
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (h : PartialEmbeddedIntersections
      (A := A) (C := C) (T := T) S f) :
    LocallyTreeLike.EmbeddedIntersections
      (A := A) (C := C) (T := T) S f := by
  intro α
  let H : Set U := {a : U | α a ∈ S}
  let e : Embedding (A.induce H) C :=
    α.comp (inclusion A H)
  have hRange : ∀ x, e x ∈ S := fun x => x.2
  obtain ⟨eHT, heHT, hc⟩ := h H e hRange
  exact ⟨eHT, heHT, hc⟩

end PartialEmbeddedIntersections

/-- Local tree witnesses carrying partial-A compatibility. -/
def PartialCompatibleLocallyTreeLike
    {V : Type v} (B : RelStructure L V)
    (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        PartialEmbeddedIntersections
          (A := A) (C := C) (T := Target) S f

namespace PartialCompatibleLocallyTreeLike

variable {V : Type v} {B : RelStructure L V}
variable {D : RelStructure L X}
variable {m n : ℕ}

/-- Monotonicity in the test-size bound. -/
theorem mono
    (h : PartialCompatibleLocallyTreeLike (A := A) B C n)
    (hmn : m ≤ n) :
    PartialCompatibleLocallyTreeLike (A := A) B C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- Pull partial compatibility back along an induced embedding. -/
theorem pullback_embedding
    (hC : PartialCompatibleLocallyTreeLike (A := A) B C n)
    (e : Embedding D C) :
    PartialCompatibleLocallyTreeLike (A := A) B D n := by
  classical
  intro S hS
  let I : Finset W := S.image e
  have hcard : I.card = S.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Z, Target, hTree, fC, hfC, hPartialC⟩ :=
    hC I (by simpa [hcard] using hS)
  let eS : ↥(↑S : Set X) → ↥(↑I : Set W) :=
    fun x => ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  let ee : Embedding (D.induce (↑S : Set X))
      (C.induce (↑I : Set W)) := {
    toFun := eS
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change C.rel R (e ∘ (Subtype.val ∘ x)) ↔
        D.rel R (Subtype.val ∘ x)
      exact e.map_rel_iff R (Subtype.val ∘ x)
  }
  let f : ↥(↑S : Set X) → Z := fC ∘ ee
  have hf :
      (D.induce (↑S : Set X)).IsHomomorphismEmbedding Target f :=
    hfC.comp ee.isHomomorphismEmbedding
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro H q hRange
  let eq : Embedding (A.induce H) C := e.comp q
  have hRangeI : ∀ x, eq x ∈ I := by
    intro x
    exact Finset.mem_image.mpr ⟨q x, hRange x, rfl⟩
  obtain ⟨qT, hqT, hc⟩ := hPartialC H eq hRangeI
  refine ⟨qT, ?_, hc⟩
  intro x
  change qT x = fC (ee ⟨q x, hRange x⟩)
  rw [hqT x]
  apply congrArg fC
  apply Subtype.ext
  rfl

end PartialCompatibleLocallyTreeLike
end StructuralRamsey.RelStructure
