import PartiteConstruction.Functional.GeneratedTreeCompletion

/-! # Projected-history tree witnesses for closed functional tests

This is the function-language counterpart of the relational
ProjectedPartialIntersections / ProjectedHistoryLocallyTreeLike invariant.

The important simplification is that every partial A-intersection occurring
here is a genuine closed substructure of A.  In the function language this is
forced automatically when a closed tested substructure meets a full A-copy:
the intersection is the preimage of a closed set under a full embedding.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W Y V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {T : Structure L Y}
variable {Base : Structure L V}

/-- Coherent embeddings of all closed tested pieces of ambient A-copies whose
projection is the restriction of a genuine full A -> D embedding. -/
def FunctionalProjectedPartialIntersections
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S),
    ∃ eHT : Embedding (A.induce H hH) T,
      (∀ x, eHT x = f ⟨e x, hRange x⟩) ∧
      eHT.ContainedInIrreducible

/-- Equality in a target witness remembers any requested finite list of
membership predicates after projection to D.  This is precisely the
root-isolation information needed by functional witness gluing. -/
def FunctionalRespectsProjectedHistory
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y)
    (history : List (Set P)) : Prop :=
  ∀ H ∈ history, ∀ x y : ↥(↑S : Set W),
    f x = f y → (p x.1 ∈ H ↔ p y.1 ∈ H)

/-- Generator-rank version of projected-history local tree completion.
Only genuine closed tested substructures occur. -/
def FunctionalProjectedHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ history : List (Set P),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory p S f history

namespace Embedding.ContainedInIrreducible

/-- Containment in an irreducible functional piece survives
postcomposition by a full embedding of the target. -/
theorem postcomp
    {H Z : Type v} {E : Structure L H}
    {e : Embedding E T} (hc : e.ContainedInIrreducible)
    {T' : Structure L Z} (j : Embedding T T') :
    (j.comp e).ContainedInIrreducible := by
  rcases hc with ⟨X, R, hR, k, hk⟩
  refine ⟨X, R, hR, j.comp k, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := hk a
  exact ⟨x, congrArg j hx⟩

end Embedding.ContainedInIrreducible

namespace FunctionalProjectedHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hgen history
  exact h S hS (hgen.mono hmn) history

/-- A witness whose kernel refines the part projection respects every finite
history list. -/
theorem respectsHistory_of_kernel_refines_projection
    {S : Finset W} {f : ↥(↑S : Set W) → Y}
    (hkern : ∀ x y : ↥(↑S : Set W),
      f x = f y → p x.1 = p y.1)
    (history : List (Set P)) :
    FunctionalRespectsProjectedHistory p S f history := by
  intro H _ x y hxy
  rw [hkern x y hxy]

end FunctionalProjectedHistoryTreeLike

/-- If a closed test is cut out from a full A-copy, its pullback subset of A
is closed. -/
theorem closedAmbientIntersection
    (α : Embedding A C)
    (S : Set W) (hS : C.IsClosed S) :
    A.IsClosed {a | α a ∈ S} :=
  closed_preimage α S hS

end StructuralRamsey.Structure
