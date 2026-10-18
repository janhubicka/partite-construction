import PartiteConstruction.Functional.LocalDomainClosedImage
import PartiteConstruction.Functional.UnaryClosedEHNHistoryShadow

/-!
# All-arity closed strict history pullback under LOCAL EHN domain reflection

The stage-relative \`AtMostClosedWithPart\` invariant counts only
genuinely function-CLOSED exact finite tests and retains strict
FULL-functional Base-tree targets, actual ambient full A-copy
intersection certificates, and arbitrary projected histories
in an INDEPENDENT fixed original control P.

A general EHN/original-2019 partial projection q:C→D may fail
global total-fibre surjectivity only at SOURCE-UNDEFINED inputs.
The local \`Structure.NoPhantomOn C D q S\` predicate excludes
precisely those failures on input tuples of one exact test S.
If S is function-closed, the verified all-arity local EHN
image-closedness lemma makes its LITERAL image q[S] closed in D.

The closed predecessor AtMostClosedWithPart of D therefore supplies
a strict target on the finite projected image without taking any
closure hull. The existing EHN commuting-parts weak-history pullback
then transfers that witness to the ORIGINAL S. The SAME rank budget,
actual full A-copy intersections and projected histories survive.

The exact-test theorem requires NoPhantomOn only on THIS S; the
optional global wrapper quantifies this condition over all closed
S of rank at most n. Neither theorem asserts that native HJ
stages automatically satisfy the no-phantom hypothesis, nor
solves maximal nonclosed relative TARGET root completion.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMostClosedWithPart

universe u v
variable {L : Language.{u}}
variable {UA VB W V P : Type v}

/-- All-arity strict full-functional B-tree HISTORY pullback on ONE
exact finite CLOSED S of size ≤n through an EHN shadow q:C→D.

Only source-domain reflection on input tuples belonging to this
specific S is required; no global full function homomorphism.
The projected image q[S] is literal and closed, its cardinal at
most |S|, and all actual full ambient A-copy intersections plus
arbitrary original-P projected histories are protected. -/
theorem exact_pullback_ehn_of_noPhantom
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    [DecidableEq V]
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x : W, pC x = pD (q x))
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : SetAmbientRelativeWeakTreeWitness.AtMostClosedWithPart
      A Base D pD n)
    (S : Finset W) (hS : S.card ≤ n)
    (hClosed : C.IsClosed (↑S : Set W))
    (hNo : C.NoPhantomOn D q (↑S : Set W))
    (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness
      A Base C pC (↑S : Set W) history := by
  classical
  let I : Finset V := S.image q
  have hImage :
      (↑I : Set V) = q '' (↑S : Set W) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hICard : I.card ≤ n :=
    (Finset.card_image_le).trans hS
  have hIClosed : D.IsClosed (↑I : Set V) := by
    rw [hImage]
    exact hq.image_isClosed_of_noPhantom
      (↑S : Set W) hClosed hNo
  have hOld : SetAmbientRelativeWeakTreeWitness
      A Base D pD (q '' (↑S : Set W)) history := by
    rw [← hImage]
    exact hD I hICard hIClosed history
  exact SetAmbientRelativeWeakTreeWitness.pullback_ehn_commutingParts
    pC pD q hq hParts hA (↑S : Set W) history hOld

/-- Uniform all-arity closed-test strict history pullback, under
the stated test-local no-phantom condition on EVERY exact
closed test of size ≤n. This premise is intentionally visible:
it is automatic for unary EHN but false for arbitrary-arity
native functional EHN stages. -/
theorem pullback_ehn_of_noPhantomOnClosed
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    [DecidableEq V]
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x : W, pC x = pD (q x))
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : SetAmbientRelativeWeakTreeWitness.AtMostClosedWithPart
      A Base D pD n)
    (hNo : ∀ (S : Finset W), S.card ≤ n →
      C.IsClosed (↑S : Set W) →
      C.NoPhantomOn D q (↑S : Set W)) :
    SetAmbientRelativeWeakTreeWitness.AtMostClosedWithPart
      A Base C pC n := by
  intro S hS hClosed history
  exact exact_pullback_ehn_of_noPhantom
    pC pD q hq hParts hA n hD S hS hClosed
    (hNo S hS hClosed) history

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.AtMostClosedWithPart
