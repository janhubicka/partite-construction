import PartiteConstruction.Functional.OriginalPartialWeakImage

/-! # Vertex rank of the original-partial weak-image transfer

This is the precise finite size bookkeeping for the small-image branch
of a potential strict functional sparsening induction with the ORIGINAL
2019 homomorphism-embedding convention.

The source test is function-closed. Its projected image is weakly induced
on exactly its *set-theoretic* image, not on a generated closure hull.
An existing strict completion of that weak target image can therefore
be pulled back without enlarging the bound.

Crucially, the premise below assumes strict completion of all relevant
weak image tests in D. It is NOT a consequence of the currently checked
closed-test local invariant, and is NOT asserted by the native EHN
weak-graph local invariant. The remaining mixed-root argument must
supply this premise or replace it with a more refined invariant.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {VB U V : Type v}
variable {Base : Structure L VB}
variable {C : Structure L U} {D : Structure L V}
variable [DecidableEq V]
variable {m : ℕ}

/-- A bounded original-partial strict-tree transfer when the
previous stage can complete each *weakly induced* image of at most m
vertices. No domain reflection and no function-closure inflation. -/
theorem HasOriginalPartialTreeCompletion.of_closed_EHN_smallWeakImage
    {p : U → V}
    (hD : ∀ I : Finset V, I.card ≤ m →
      HasOriginalPartialTreeCompletion Base
        (D.weakInduce (↑I : Set V)))
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Finset U) (hS : C.IsClosed (↑S : Set U))
    (hImageSize : (S.image p).card ≤ m) :
    HasOriginalPartialTreeCompletion Base
      (C.induce (↑S : Set U) hS) := by
  classical
  let I : Finset V := S.image p
  let inc : Embedding (C.induce (↑S : Set U) hS) C :=
    inclusion C (↑S : Set U) hS
  have hsmall :
      (C.induce (↑S : Set U) hS).IsEHNHomomorphismEmbedding
        D (p ∘ Subtype.val) :=
    hp.comp inc.isEHNHomomorphismEmbedding
  have hRange : ∀ x : ↥(↑S : Set U),
      (p ∘ Subtype.val) x ∈ (↑I : Set V) := by
    intro x
    exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
  have hProjection :
      IsOriginalPartialHomomorphismEmbedding
        (C.induce (↑S : Set U) hS)
        (D.weakInduce (↑I : Set V))
        (fun x => (⟨p x.1, hRange x⟩ : ↥(↑I : Set V))) :=
    hsmall.toOriginalPartial.codRestrictWeak (↑I : Set V) hRange
  have hI : I.card ≤ m := hImageSize
  exact (hD I hI).pullback hProjection

end StructuralRamsey.Structure
