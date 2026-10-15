import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Projected A-copy histories for strict original-2019 partial B-tree targets

An adversarial finite C5 example shows why two arbitrary EHN stages,
each merely locally strict B-tree completable, need not have a strict
completion after one native selected-support attachment. The missing
data is not just the generator bound or a flexible common root map:
one must preserve the published Hales--Jewett Picture's projected
A-copy/intersection constraints through the induction.

The existing `FunctionalProjectedHistoryTreeLike` records coherent
projected partial A-copies and finite colour/history diaries, but
requires the stronger later-survey FULL function-fibre homomorphism.
This module introduces the SOURCE-FAITHFUL version for original-2019
partial functions: target trees and all A-intersection embeddings are
genuine FULL functional, while the global test map is only an
original-partial homomorphism-embedding (equivalently EHN).

The definition is an invariant / proof interface, not a statement
that the mixed Picture preservation or hard-root extension is known.
The base and weakening lemmas are unconditional, kernel-checkable
foundations for a future genuine Hales--Jewett trace proof.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W VB : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L VB}

/-- Closed generator-rank strict B-tree witnesses in the literal
original 2019 partial-function convention, with BOTH:
* coherent embeddings of every tested closed partial A-copy, contained
  in a genuine irreducible B-constituent; and
* arbitrary finite projected-history diaries.

The global test map does NOT reflect the domain of undefined source
functions. The target B-tree and the protected A-piece embeddings
remain full functional structures and full embeddings. -/
def FunctionalOriginalPartialProjectedHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ history : List (Set P),
      ∃ (Z : Type v) (Target : Structure L Z),
        TreeAmalgam Base Z Target ∧
        ∃ f : ↥(↑S : Set W) → Z,
          IsOriginalPartialHomomorphismEmbedding
            (C.induce (↑S : Set W) hS) Target f ∧
          FunctionalProjectedPartialIntersections
            (A := A) (D := D) (C := C) (T := Target) p S f ∧
          FunctionalRespectsProjectedHistory p S f history

namespace FunctionalOriginalPartialProjectedHistoryTreeLike

/-- Restricting the permissible generator count preserves the
original-partial projected-history invariant. -/
theorem mono
    {p : W → P} {m n : ℕ}
    (h : FunctionalOriginalPartialProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalOriginalPartialProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hGen history
  exact h S hS (hGen.mono hmn) history

/-- Every witness in the later stronger FULL homomorphism-embedding
sense is also a witness for original-2019 partial functions. This
direction does NOT identify the two homomorphism notions. -/
theorem of_full
    {p : W → P} {n : ℕ}
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalOriginalPartialProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  intro S hS hGen history
  obtain ⟨Z, Target, hTree, f, hf, hA, hHistory⟩ :=
    h S hS hGen history
  have hp : IsOriginalPartialHomomorphismEmbedding
      (C.induce (↑S : Set W) hS) Target f := by
    refine ⟨⟨hf.1.1, ?_⟩, hf.2⟩
    intro F x _hDef
    exact hf.1.2 F x
  exact ⟨Z, Target, hTree, f, hp, hA, hHistory⟩

/-- The irreducible base itself satisfies the stronger profile and
history invariant at EVERY generator rank, for any outer projection
p and any control D. For every full tested partial A-copy the
completion map is the full inclusion into Base, hence its image
already lies inside the constituent Base-copy.

In particular no global fixed original A-support root labels or
extra closure vertices are required in this initial witness. -/
theorem base
    (Base : Structure L VB) (hBase : Base.Irreducible)
    (p : VB → P) (n : ℕ) :
    FunctionalOriginalPartialProjectedHistoryTreeLike
      (A := A) (D := D) (C := Base) (Base := Base) p n := by
  intro S hS _hGen history
  let inc : Embedding (Base.induce (↑S : Set VB) hS) Base :=
    inclusion Base (↑S : Set VB) hS
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  have hPartial : IsOriginalPartialHomomorphismEmbedding
      (Base.induce (↑S : Set VB) hS) Base inc :=
    inc.isEHNHomomorphismEmbedding.toOriginalPartial
  refine ⟨VB, Base, hTree, inc, hPartial, ?_, ?_⟩
  · intro β H hH e _hProj hRange
    let full : Embedding (A.induce H hH) Base := e
    refine ⟨full, (fun _ => rfl), ?_⟩
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro x
    exact ⟨full x, rfl⟩
  · intro H _hH x y hxy
    have hEq : x = y := inc.injective hxy
    subst y
    rfl

end FunctionalOriginalPartialProjectedHistoryTreeLike

end StructuralRamsey.Structure
