import PartiteConstruction.Functional.EHNCommonParameterFamily
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Exact strict weak-history locality for common-coordinate HJ families

This is the vertex-EXACT local sparsening consequence of the
simultaneous EHN shadow of a finite family of genuine Hales--Jewett
lines with ONE common parameter coordinate.

The verified shadow back to the old functional Picture commutes with
the fixed control parts. Pulling back its existing strict full-
functional Base-tree witnesses therefore preserves, at the SAME
n-vertex bound:

* arbitrary exact weak subsets, without taking their function hulls;
* original-2019 ambient-relative function behaviour (no false domain
  reflection on undefined inputs);
* genuine ambient full A-copy intersections;
* arbitrary finite projected histories of the ORIGINAL control.

This is a many-attachment strict-function theorem. It is not a proof
of the unrestricted all-line Hales--Jewett Picture: a family of lines
with no common parameter coordinate can defeat common retraction and
requires the still missing mixed-root/history induction.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}}
variable {P V U VB : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- A finite family of full HJ line attachments sharing a parameter
coordinate inherits the OLD Picture's complete strict FULL-functional
n-vertex weak-history invariant.

No singleton-valuedness or bounded generated-hull assumption: this
is directly an EHN projection / exact weak-image cardinality transfer.
Every intermediate stage is a genuine transversal functional System. -/
theorem commonParameterLines_strictWeakHistory
    (hK : Structure.FreeAmalgamationClass K)
    (B : System L P V) [Finite V]
    (hB : B.WeaklyPartiteOver D) (hmB : K B.toStructure)
    (A : Structure L U) [Finite U] [Finite P]
    (hKA : K A) (hA : A.Irreducible)
    (Base : Structure L VB) (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMost
      A Base B.toStructure B.part n)
    (alpha : Structure.Embedding A D)
    (N : ℕ) (hN : 0 < N) (i : Fin N)
    (xs : List {W : Line
      (Induced.Letter A (B.weakRestrict D hB.1 A alpha)) N //
        W.symbol i = .parameter}) :
    ∃ T : Stage K D,
      SetAmbientRelativeWeakTreeWitness.AtMost
        A Base T.system.toStructure T.system.part n := by
  classical
  obtain ⟨T, _core, q, hq, _hqCore, hPart, _hCopies⟩ :=
    commonParameterLines_partCompatibleEHNShadow
      hK B hB hmB A hKA alpha N hN i xs
  refine ⟨T, ?_⟩
  exact SetAmbientRelativeWeakTreeWitness.AtMost.pullback_ehn_commutingParts
    T.system.part B.part q hq (fun z => (hPart z).symm)
    hA n hOld

end StructuralRamsey.FunctionalPartite.EHN
