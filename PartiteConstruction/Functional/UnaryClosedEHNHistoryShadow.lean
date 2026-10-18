import PartiteConstruction.Functional.ClosedControlStrictPredecessor
import PartiteConstruction.Functional.UnaryEHNCompletion
import PartiteConstruction.Functional.PowerCoordinateEHN
import PartiteConstruction.Structure.HomImageClosed
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Unary closed-test strict history transfer through EHN shadows and native HJ power

The weaker \`AtMostClosed\` strict functional predecessor on the
full functional control D requires B-tree weak-history witnesses
ONLY for exact function-closed finite subsets. To run the NATIVE
Hales--Jewett Picture iteration we retain separate ORIGINAL control
part maps, rather than identifying the moving previous-stage carrier
with the original control.

\`AtMostClosedWithPart\` is the closed-only strict witness invariant
on a genuine functional stage C with pC:C→P. It retains actual
ambient full A-copy intersections and arbitrary finite projected
histories of the FIXED original P.

If q:C→D is an EHN original-partial map in a UNARY function
language, the verified unary-domain theorem upgrades it to a
FULL functional homomorphism. Its image of a CLOSED exact source
S is CLOSED in D, so the preceding AtMostClosedWithPart witness
on the literal finite image q[S] pulls back at the SAME cardinal
bound via the verified EHN history/ambient A-copy pullback.

The ACTUAL native functional HJ coordinate power has an EHN
coordinate map (previously verified), with commuting part maps.
Thus the whole power inherits closed-only strict functional
history locality at the same rank as its predecessor, without
a relational proxy or a function closure of the tested subset.

This certifies the unary PURE HJ POWER transfer, NOT the remaining
copied-old or genuine mixed finite line-attachment induction.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB W V P : Type v}

/-- Closed-only strict full-functional B-tree history locality
for a genuine functional stage C with an independent projection
p:C→P into the ORIGINAL control part carrier.

Only exact finite CLOSED S are tested. Their vertex cardinality,
not that of their generated closure, is charged against n.
The target retains full ambient A-intersections and histories
of the original P. -/
def AtMostClosedWithPart
    (A : Structure L UA) (Base : Structure L VB)
    (C : Structure L W) (p : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    C.IsClosed (↑S : Set W) →
    ∀ history : List (Set P),
      SetAmbientRelativeWeakTreeWitness
        A Base C p (↑S : Set W) history

/-- The existing closed-control-only predecessor is exactly the
stage-relative predicate with identity part projection. -/
theorem atMostClosed_iff_withPart_id
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P} {n : ℕ} :
    AtMostClosed A Base D n ↔
      AtMostClosedWithPart A Base D (id : P → P) n :=
  Iff.rfl

namespace AtMostClosedWithPart

/-- Pull the closed-only strict witness invariant back through
any unary EHN projection q:C→D commuting with the ORIGINAL
control part maps pC and pD.

In unary function languages the EHN map is FULL, so a closed
exact S has CLOSED literal finite image q[S]. The already
verified EHN relative-history pullback keeps the same strict
full-functional B-tree target, actual full ambient A-copy
intersections, and all original-P projected histories.
No rank/cardinality inflation or global injectivity of q. -/
theorem pullback_ehn_unary
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    (hUnary : L.UnaryFuncArity)
    [DecidableEq V]
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x : W, pC x = pD (q x))
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : AtMostClosedWithPart A Base D pD n) :
    AtMostClosedWithPart A Base C pC n := by
  classical
  intro S hS hClosed history
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
    exact (hq.isHomomorphism_of_unary hUnary).image_isClosed
      (↑S : Set W) hClosed
  have hOld : SetAmbientRelativeWeakTreeWitness
      A Base D pD (q '' (↑S : Set W)) history := by
    rw [← hImage]
    exact hD I hICard hIClosed history
  exact SetAmbientRelativeWeakTreeWitness.pullback_ehn_commutingParts
    pC pD q hq hParts hA (↑S : Set W) history hOld

end AtMostClosedWithPart

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}} {P V UA VB : Type v}

/-- The ACTUAL genuine functional Hales--Jewett coordinate power
preserves the closed-only strict full-functional B-tree history
invariant at the SAME rank n in a unary function language.

The coordinating map is a real coordinate evaluation, verified
EHN on full irreducibles. Its output-part labels match the part
of every power vertex at that coordinate. The source power still
has genuine transversal set-valued function outputs. -/
theorem power_closedHistory_unary
    (hUnary : L.UnaryFuncArity)
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    [DecidableEq V]
    {A : Structure L UA} {Base : Structure L VB}
    (hA : A.Irreducible)
    (N : ℕ) (hN : 0 < N) (n : ℕ)
    (hOld : AtMostClosedWithPart
      A Base B.toStructure B.part n) :
    AtMostClosedWithPart
      A Base (power B N).toStructure (power B N).part n := by
  let i : Fin N := ⟨0, hN⟩
  let q : Vertex B N → V := fun z => z.coord i
  have hq : (power B N).toStructure.IsEHNHomomorphismEmbedding
      B.toStructure q :=
    coordinateEHN hB hN i
  have hParts : ∀ z : Vertex B N,
      (power B N).part z = B.part (q z) := by
    intro z
    exact (z.belongs i).symm
  exact AtMostClosedWithPart.pullback_ehn_unary
    hUnary (power B N).part B.part q hq hParts hA n hOld

end StructuralRamsey.FunctionalPartite.Induced
