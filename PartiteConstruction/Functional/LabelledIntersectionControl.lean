import PartiteConstruction.Functional.QuotientBoundaryDiary
import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Structure.IrreducibleHomImage

/-! # Functional labelled quotient roots for closed intersections

For relational sparsening, a reducible intersection with an ambient A-copy is
controlled by recording the A-label of every tested point in one target
A-copy. The labels may identify vertices, so the natural gluing root is the
quotient given by their image in A.

For full relation/function structures there is one extra point: the label
image has to be closed under every function fibre. On a closed test this is
automatic. The witness map and the boundary inclusion are full
homomorphisms, the target A-copy is a full embedding, and cancellation shows
that the label map itself is a full homomorphism. Hence its range is closed.

This is the functional counterpart of the relational labelled-intersection
control file.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U W Y : Type v}
variable {A : Structure L U}
variable {C : Structure L W}
variable {T : Structure L Y}

/-- Full homomorphisms cancel through a full embedding. -/
theorem Embedding.cancelHomomorphism
    {X₀ X₁ X₂ : Type v}
    {A₀ : Structure L X₀} {A₁ : Structure L X₁}
    {A₂ : Structure L X₂}
    (j : Embedding A₁ A₂) {g : X₀ → X₁}
    (h : A₀.IsHomomorphism A₂ (j ∘ g)) :
    A₀.IsHomomorphism A₁ g := by
  constructor
  · intro R x hx
    exact (j.map_rel_iff R (g ∘ x)).mp (h.1 R x hx)
  · intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have htarget :
          j (g z) ∈ A₂.func F (j ∘ (g ∘ x)) := by
        have himg :
            (j ∘ g) z ∈ imageSet (j ∘ g) (A₀.func F x) :=
          ⟨z, hz, rfl⟩
        rw [h.2 F x] at himg
        simpa [Function.comp_assoc] using himg
      have himg :
          j (g z) ∈ imageSet j (A₁.func F (g ∘ x)) := by
        rw [j.map_func F (g ∘ x)]
        exact htarget
      rcases himg with ⟨b, hb, hbeq⟩
      exact j.injective hbeq ▸ hb
    · intro hy
      have hj :
          j y ∈ A₂.func F ((j ∘ g) ∘ x) := by
        have himg :
            j y ∈ imageSet j (A₁.func F (g ∘ x)) :=
          ⟨y, hy, rfl⟩
        rw [j.map_func F (g ∘ x)] at himg
        simpa [Function.comp_assoc] using himg
      have hpre :
          j y ∈ imageSet (j ∘ g) (A₀.func F x) := by
        rw [h.2 F x]
        exact hj
      rcases hpre with ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      apply j.injective
      exact hzy

/-- The A-preimage of a closed tested set is closed. -/
def labelledBoundarySet
    (S : Finset W) (α : Embedding A C) : Set U :=
  {a | α a ∈ S}

theorem labelledBoundarySet_closed
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (α : Embedding A C) :
    A.IsClosed (labelledBoundarySet S α) := by
  exact α.preimage_isClosed (↑S : Set W) hS

/-- A tested closed intersection with an ambient A-copy, labelled inside one
target A-copy. Labels are allowed to identify boundary vertices. -/
structure FunctionalLabelledIntersectionControl
    (S : Finset W)
    (f : ↥(↑S : Set W) → Y)
    (α : Embedding A C) where
  targetCopy : Embedding A T
  label : ↥(labelledBoundarySet S α) → U
  agrees : ∀ x,
    f ⟨α x.1, x.2⟩ = targetCopy (label x)

namespace FunctionalLabelledIntersectionControl

variable {S : Finset W}
variable {f : ↥(↑S : Set W) → Y}
variable {α : Embedding A C}

/-- Ordinary whole-A control canonically supplies quotient labels on the tested
intersection. -/
noncomputable def of_control
    (targetCopy : Embedding A T)
    (hctrl : ∀ a : U, ∀ ha : α a ∈ S,
      ∃ a' : U, f ⟨α a, ha⟩ = targetCopy a') :
    FunctionalLabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α where
  targetCopy := targetCopy
  label := fun x => Classical.choose (hctrl x.1 x.2)
  agrees := fun x => Classical.choose_spec (hctrl x.1 x.2)

/-- Package every ordinary ambient-copy control choice as functional labelled
quotient data. -/
theorem of_controls
    (hctrl :
      ∀ α : Embedding A C,
        ∃ α' : Embedding A T,
          ∀ a : U, ∀ ha : α a ∈ S,
            ∃ a' : U, f ⟨α a, ha⟩ = α' a') :
    ∀ α : Embedding A C,
      Nonempty
        (FunctionalLabelledIntersectionControl
          (A := A) (C := C) (T := T) S f α) := by
  intro β
  obtain ⟨β', hβ'⟩ := hctrl β
  exact ⟨of_control β' hβ'⟩

/-- The full boundary substructure cut out by a closed test. -/
abbrev boundary
    (hS : C.IsClosed (↑S : Set W)) :
    Structure L ↥(labelledBoundarySet S α) :=
  A.induce (labelledBoundarySet S α)
    (labelledBoundarySet_closed S hS α)

/-- Embed the closed A-boundary into the closed tested substructure. -/
noncomputable def boundaryEmbedding
    (hS : C.IsClosed (↑S : Set W)) :
    Embedding (boundary (A := A) (α := α) hS)
      (C.induce (↑S : Set W) hS) := by
  let incA :
      Embedding (boundary (A := A) (α := α) hS) A :=
    inclusion A (labelledBoundarySet S α)
      (labelledBoundarySet_closed S hS α)
  let eAmbient :
      Embedding (boundary (A := A) (α := α) hS) C :=
    α.comp incA
  let incC :
      Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  let q :
      ↥(labelledBoundarySet S α) → ↥(↑S : Set W) :=
    fun x => ⟨α x.1, x.2⟩
  exact eAmbient.factorWithMap incC q (fun _ => rfl)

/-- The chosen label map is automatically a full homomorphism on a closed
test. -/
theorem label_isHomomorphism
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    (boundary (A := A) (α := α) hS).IsHomomorphism A h.label := by
  let e := boundaryEmbedding (A := A) (α := α) hS
  have hcomp :
      (boundary (A := A) (α := α) hS).IsHomomorphism T
        (f ∘ e) :=
    hf.comp e.isHomomorphism
  have heq :
      f ∘ e = h.targetCopy ∘ h.label := by
    funext x
    exact h.agrees x
  rw [heq] at hcomp
  exact h.targetCopy.cancelHomomorphism hcomp

/-- The label image is therefore a closed subset of A. -/
def labelRange
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α) :
    Set U :=
  Set.range h.label

theorem labelRange_closed
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    A.IsClosed h.labelRange :=
  (h.label_isHomomorphism hS hf).range_isClosed

/-- The genuine functional quotient root induced by the labels. -/
abbrev root
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    Structure L h.labelRange :=
  A.induce h.labelRange (h.labelRange_closed hS hf)

/-- Quotient map from the original closed boundary to its closed label image. -/
def quotient
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α) :
    ↥(labelledBoundarySet S α) → h.labelRange :=
  fun x => ⟨h.label x, ⟨x, rfl⟩⟩

theorem quotient_surjective
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α) :
    Function.Surjective h.quotient := by
  intro z
  rcases z.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- The quotient map is a full homomorphism onto the closed label root. -/
theorem quotient_isHomomorphism
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    (boundary (A := A) (α := α) hS).IsHomomorphism
      (h.root hS hf) h.quotient := by
  have hl := h.label_isHomomorphism hS hf
  let hclosed : A.IsClosed h.labelRange :=
    h.labelRange_closed hS hf
  have hc :
      (boundary (A := A) (α := α) hS).IsHomomorphism
        (A.induce h.labelRange hclosed)
        (fun x => ⟨h.label x, ⟨x, rfl⟩⟩) :=
    hl.codRestrict h.labelRange hclosed (fun x => ⟨x, rfl⟩)
  change
    (boundary (A := A) (α := α) hS).IsHomomorphism
      (A.induce h.labelRange hclosed)
      (fun x => ⟨h.label x, ⟨x, rfl⟩⟩)
  exact hc

/-- The quotient root embeds into the target inside the controlled A-copy. -/
def rootEmbedding
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    Embedding (h.root hS hf) T :=
  h.targetCopy.comp
    (inclusion A h.labelRange (h.labelRange_closed hS hf))

theorem rootEmbedding_quotient
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f)
    (x : ↥(labelledBoundarySet S α)) :
    h.rootEmbedding hS hf (h.quotient x) =
      f ⟨α x.1, x.2⟩ := by
  exact (h.agrees x).symm

/-- If A is irreducible, the quotient root embedding is contained in the
irreducible target copy of A. -/
theorem rootEmbedding_contained
    (hA : A.Irreducible)
    (h :
      FunctionalLabelledIntersectionControl
        (A := A) (C := C) (T := T) S f α)
    (hS : C.IsClosed (↑S : Set W))
    (hf :
      (C.induce (↑S : Set W) hS).IsHomomorphism T f) :
    (h.rootEmbedding hS hf).ContainedInIrreducible := by
  refine ⟨U, A, hA, h.targetCopy, ?_⟩
  intro z
  exact ⟨z.1, rfl⟩

end FunctionalLabelledIntersectionControl

end StructuralRamsey.Structure
