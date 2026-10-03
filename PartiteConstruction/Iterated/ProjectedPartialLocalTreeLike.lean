import PartiteConstruction.Iterated.ControlCompletionCompatible

/-! # Projection-compatible partial A-intersections

The iterated Picture construction does not need coherence for arbitrary
partial A-copies.  The relevant partial copies are those whose projection to
the current base D is the restriction of a genuine full embedding
beta : A -> D.  These are exactly the boundaries produced when a future
ambient A-copy meets an old attached copy.

This history-sensitive invariant is designed to be inductive through Picture
steps while remaining strong enough for reducible overlaps.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U P W Y X : Type v}
variable {A : RelStructure L U} {D : RelStructure L P}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Coherent target embeddings for all tested partial A-copies whose
projection is the restriction of a full A -> D embedding. -/
def ProjectedPartialIntersections
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ (β : Embedding A D) (H : Set U)
    (e : Embedding (A.induce H) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S),
    ∃ eHT : Embedding (A.induce H) T,
      (∀ x, eHT x = f ⟨e x, hRange x⟩) ∧
      eHT.ContainedInIrreducible

/-- Local tree witnesses carrying projection-compatible partial-A data. -/
def ProjectedPartialLocallyTreeLike
    {V : Type v} (B : RelStructure L V)
    (p : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        ProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f

namespace ProjectedPartialLocallyTreeLike

variable {V : Type v} {B : RelStructure L V}
variable {C' : RelStructure L X}
variable {p : W → P} {p' : X → P}
variable {m n : ℕ}

/-- Monotonicity in the test-size bound. -/
theorem mono
    (h : ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p n)
    (hmn : m ≤ n) :
    ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- Pull the projected invariant back along an induced embedding that
commutes with the projections. -/
theorem pullback_embedding
    (hC : ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p n)
    (e : Embedding C' C)
    (hproj : ∀ x, p' x = p (e x)) :
    ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C') B p' n := by
  classical
  intro S hS
  let I : Finset W := S.image e
  have hcard : I.card = S.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Z, Target, hTree, fC, hfC, hPartC⟩ :=
    hC I (by simpa [hcard] using hS)
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
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
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
  obtain ⟨qT, hqT, hc⟩ :=
    hPartC β H qC hqprojC hqRangeC
  refine ⟨qT, ?_, hc⟩
  intro x
  change qT x = fC (ee ⟨q x, hqRange x⟩)
  rw [hqT x]
  apply congrArg fC
  apply Subtype.ext
  rfl

/-- A projected invariant gives ordinary embedded intersections for full
ambient A-copies whenever p is a homomorphism-embedding into D. -/
theorem embeddedIntersections
    (hA : A.Irreducible)
    (hp : C.IsHomomorphismEmbedding D p)
    {S : Finset W} {Z : Type v} {Target : RelStructure L Z}
    {f : ↥(↑S : Set W) → Z}
    (hPart :
      ProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := Target) p S f) :
    LocallyTreeLike.EmbeddedIntersections
      (A := A) (C := C) (T := Target) S f := by
  intro α
  obtain ⟨β, hβ⟩ := hp.after_irreducible_embedding hA α
  let H : Set U := {a : U | α a ∈ S}
  let e : Embedding (A.induce H) C :=
    α.comp (inclusion A H)
  have heproj : ∀ x, p (e x) = β x.1 := by
    intro x
    exact (hβ x.1).symm
  have heRange : ∀ x, e x ∈ S := fun x => x.2
  exact hPart β H e heproj heRange

/-- Forget projection-history data by completing the usual ambient-A
control.  Only irreducibility of A is used. -/
theorem toLocallyTreeLike
    [Finite U] [Finite W]
    (hA : A.Irreducible) (eAB : Embedding A B)
    (hp : C.IsHomomorphismEmbedding D p)
    (h : ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p n) :
    LocallyTreeLike A B C n := by
  intro S hS
  obtain ⟨Z, Target, hTree, f, hf, hPart⟩ := h S hS
  have hInt :
      LocallyTreeLike.EmbeddedIntersections
        (A := A) (C := C) (T := Target) S f :=
    embeddedIntersections hA hp hPart
  exact LocallyTreeLike.completeControl_of_embeddedIntersections
    (A := A) (B := B) (C := C)
    hA eAB S hTree f hf hInt

/-- Rebase a projected invariant to the identity projection on C.  This is
the form needed when C becomes the base structure for the next outer
iteration. -/
theorem rebase_identity
    (hA : A.Irreducible)
    (hp : C.IsHomomorphismEmbedding D p)
    (h : ProjectedPartialLocallyTreeLike
      (A := A) (D := D) (C := C) B p n) :
    ProjectedPartialLocallyTreeLike
      (A := A) (D := C) (C := C) B id n := by
  classical
  intro S hS
  obtain ⟨Z, Target, hTree, f, hf, hPart⟩ := h S hS
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro β H e heproj heRange
  obtain ⟨βD, hβD⟩ := hp.after_irreducible_embedding hA β
  have hOldProj : ∀ x, p (e x) = βD x.1 := by
    intro x
    have heq : e x = β x.1 := by
      simpa using heproj x
    rw [heq]
    exact (hβD x.1).symm
  exact hPart βD H e hOldProj heRange

end ProjectedPartialLocallyTreeLike
end StructuralRamsey.RelStructure
