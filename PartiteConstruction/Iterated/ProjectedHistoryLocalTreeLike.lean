import PartiteConstruction.Iterated.ProjectedPartialLocalTreeLike
import PartiteConstruction.Iterated.MixedOverlapExactness

/-! # Finite projected-history witnesses

The remaining mixed Picture obstruction is not irreducibility of the
construction overlap itself, but loss of quotient history: a side completion
may identify a point outside the overlap with a point inside it.

A finite history is represented by subsets of the current base D.  A witness
respects the history when equality in the target preserves membership in every
history subset after applying the part projection.  In a hard mixed step the
part projection is injective on the tested set, so adding the projected
construction overlap to the history forces exact overlap reflection.

The invariant quantifies over arbitrary finite histories supplied by the
caller.  This makes it stable under future Picture steps without storing a
globally growing list in the stage itself.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U P W Y X V : Type v}
variable {A : RelStructure L U} {D : RelStructure L P}
variable {C : RelStructure L W} {T : RelStructure L Y}
variable {B : RelStructure L V}

/-- A target witness preserves all requested membership bits on the source
test after projection to D. -/
def RespectsProjectedHistory
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y)
    (history : List (Set P)) : Prop :=
  ∀ H ∈ history, ∀ x y : ↥(↑S : Set W),
    f x = f y → (p x.1 ∈ H ↔ p y.1 ∈ H)

/-- Projected-partial local tree witnesses that can additionally respect any
finite list of requested base subsets. -/
def ProjectedHistoryLocallyTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ history : List (Set P),
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        ProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        RespectsProjectedHistory p S f history

namespace ProjectedHistoryLocallyTreeLike

variable {p : W → P} {p' : X → P}
variable {C' : RelStructure L X}
variable {m n : ℕ}

/-- Forget the history requirement. -/
theorem toProjectedPartial
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n) :
    ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p n := by
  intro S hS
  obtain ⟨Z, Target, hTree, f, hf, hPart, _⟩ :=
    h S hS []
  exact ⟨Z, Target, hTree, f, hf, hPart⟩

/-- Monotonicity in the size bound. -/
theorem mono
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n)
    (hmn : m ≤ n) :
    ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p m := by
  intro S hS history
  exact h S (hS.trans hmn) history

/-- Pull history-sensitive witnesses back along an induced embedding that
commutes with the projection. -/
theorem pullback_embedding
    (hC : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n)
    (e : Embedding C' C)
    (hproj : ∀ x, p' x = p (e x)) :
    ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C') (B := B) p' n := by
  classical
  intro S hS history
  let I : Finset W := S.image e
  have hcard : I.card = S.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Z, Target, hTree, fC, hfC, hPartC, hHistC⟩ :=
    hC I (by simpa [hcard] using hS) history
  let eS : ↥(↑S : Set X) → ↥(↑I : Set W) :=
    fun x => ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  let ee : Embedding (C'.induce (↑S : Set X))
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
        C'.rel R (Subtype.val ∘ x)
      exact e.map_rel_iff R (Subtype.val ∘ x)
  }
  let f : ↥(↑S : Set X) → Z := fC ∘ ee
  have hf :
      (C'.induce (↑S : Set X)).IsHomomorphismEmbedding Target f :=
    hfC.comp ee.isHomomorphismEmbedding
  have hPart :
      ProjectedPartialIntersections
        (A := A) (D := D) (C := C') (T := Target) p' S f := by
    intro β H q hqproj hqRange
    let qC : Embedding (A.induce H) C := e.comp q
    have hqprojC : ∀ x, p (qC x) = β x.1 := by
      intro x
      change p (e (q x)) = β x.1
      rw [← hproj (q x)]
      exact hqproj x
    have hqRangeC : ∀ x, qC x ∈ I := by
      intro x
      exact Finset.mem_image.mpr ⟨q x, hqRange x, rfl⟩
    obtain ⟨qT, hqT, hc⟩ := hPartC β H qC hqprojC hqRangeC
    refine ⟨qT, ?_, hc⟩
    intro x
    change qT x = fC (ee ⟨q x, hqRange x⟩)
    rw [hqT x]
    apply congrArg fC
    apply Subtype.ext
    rfl
  have hHist :
      RespectsProjectedHistory p' S f history := by
    intro H hH x y hxy
    have hOld :=
      hHistC H hH (eS x) (eS y) hxy
    simpa [hproj x.1, hproj y.1] using hOld
  exact ⟨Z, Target, hTree, f, hf, hPart, hHist⟩

/-- If the witness preserves equality of projected points, then it respects
every possible finite history.  This is the pattern used by pure-core
one-copy witnesses. -/
theorem respectsHistory_of_kernel_refines_projection
    {S : Finset W} {f : ↥(↑S : Set W) → Y}
    (hkern : ∀ x y : ↥(↑S : Set W),
      f x = f y → p x.1 = p y.1)
    (history : List (Set P)) :
    RespectsProjectedHistory p S f history := by
  intro H hH x y hxy
  rw [hkern x y hxy]

end ProjectedHistoryLocallyTreeLike
end StructuralRamsey.RelStructure
