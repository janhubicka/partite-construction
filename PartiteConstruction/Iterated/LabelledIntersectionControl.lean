import PartiteConstruction.Iterated.LocalTreeLike

/-! # Labelled quotient data for reducible A-intersections

Ordinary local-tree control already contains more useful information than an
unstructured containment statement.  For an ambient copy alpha : A -> C and
a finite test S, every tested point alpha(a) is sent into some target copy of
A.  Recording the corresponding target A-label gives a map from the tested
boundary into A; this map may identify vertices when the boundary is
reducible.

The image of that label map, with the induced structure from A, is a canonical
target overlap embedded inside the target A-copy.  Thus reducible boundaries
naturally carry quotient roots rather than embedded copies of themselves.

This is the data that has to be synchronized between the two sides of the
remaining mixed Picture step.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U W Y : Type v}
variable {A : RelStructure L U}
variable {C : RelStructure L W}
variable {T : RelStructure L Y}

/-- A tested intersection with an ambient A-copy, labelled inside one target
A-copy.  The label map is allowed to be non-injective. -/
structure LabelledIntersectionControl
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (α : Embedding A C) where
  targetCopy : Embedding A T
  label : ↥({a : U | α a ∈ S} : Set U) → U
  agrees : ∀ x,
    f ⟨α x.1, x.2⟩ = targetCopy (label x)

namespace LabelledIntersectionControl

variable {S : Finset W} {f : ↥(↑S : Set W) → Y}
variable {α : Embedding A C}

/-- Ordinary local-tree control canonically supplies labelled quotient data. -/
noncomputable def of_control
    (α' : Embedding A T)
    (hα' : ∀ a : U, ∀ ha : α a ∈ S,
      ∃ a' : U, f ⟨α a, ha⟩ = α' a') :
    LabelledIntersectionControl (A := A) (C := C) (T := T) S f α where
  targetCopy := α'
  label := fun x => Classical.choose (hα' x.1 x.2)
  agrees := fun x => Classical.choose_spec (hα' x.1 x.2)

/-- The label image inside A. -/
def labelRange
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) : Set U :=
  Set.range h.label

/-- The quotient root induced by the labels in A. -/
abbrev root
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) :
    RelStructure L h.labelRange :=
  A.induce h.labelRange

/-- Quotient map from the tested boundary to its labelled image. -/
def quotient
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) :
    ↥({a : U | α a ∈ S} : Set U) → h.labelRange :=
  fun x => ⟨h.label x, ⟨x, rfl⟩⟩

/-- The quotient root embeds into the target through the controlled A-copy. -/
def rootEmbedding
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) :
    Embedding h.root T :=
  h.targetCopy.comp (inclusion A h.labelRange)

/-- The quotient factorization agrees pointwise with the original witness. -/
theorem rootEmbedding_quotient
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α)
    (x : ↥({a : U | α a ∈ S} : Set U)) :
    h.rootEmbedding (h.quotient x) =
      f ⟨α x.1, x.2⟩ := by
  exact (h.agrees x).symm

/-- The quotient map is onto its root by construction. -/
theorem quotient_surjective
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) :
    Function.Surjective h.quotient := by
  intro z
  rcases z.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- If A is irreducible, the quotient root is contained in the irreducible
target copy h.targetCopy[A]. -/
theorem rootEmbedding_contained
    (hA : A.Irreducible)
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α) :
    h.rootEmbedding.ContainedInIrreducible := by
  apply Embedding.containedInIrreducible_of_range_subset
    hA h.targetCopy h.rootEmbedding
  intro z
  exact ⟨z.1, rfl⟩

/-- Postcomposition by a target embedding preserves labelled quotient data
without changing any labels. -/
def postcomp
    {Z : Type v} {T' : RelStructure L Z}
    (h : LabelledIntersectionControl
      (A := A) (C := C) (T := T) S f α)
    (j : Embedding T T') :
    LabelledIntersectionControl
      (A := A) (C := C) (T := T') S (j ∘ f) α where
  targetCopy := j.comp h.targetCopy
  label := h.label
  agrees := by
    intro x
    exact congrArg j (h.agrees x)

end LabelledIntersectionControl

/-- Package every ordinary control choice as labelled quotient data. -/
theorem labelledIntersections_of_controls
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (hctrl : ∀ α : Embedding A C,
      ∃ α' : Embedding A T,
        ∀ a : U, ∀ ha : α a ∈ S,
          ∃ a' : U, f ⟨α a, ha⟩ = α' a') :
    ∀ α : Embedding A C,
      Nonempty
        (LabelledIntersectionControl
          (A := A) (C := C) (T := T) S f α) := by
  intro α
  obtain ⟨α', hα'⟩ := hctrl α
  exact ⟨LabelledIntersectionControl.of_control α' hα'⟩

end StructuralRamsey.RelStructure.LocallyTreeLike
