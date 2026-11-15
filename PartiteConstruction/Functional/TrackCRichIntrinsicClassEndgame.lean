import PartiteConstruction.Functional.TrackCRichSameSelectedHEOnClosed
import PartiteConstruction.Functional.TrackCRichHEArrowTransfer

/-!
# Track C: conditional ORIGINAL intrinsic class-local rich Ramsey endgame

This is an English-first literal theorem-contract check. No additional
K-completion oracle is to be silently inserted into the printed proof:
the intrinsic local-completion axiom is stated in the genuine
Option(Set) language, its map is the original source-defined
homomorphism-embedding, and B-copy coverage means an ACTUAL B→D
full embedding INSIDE D.

Given ONE actual second witness D with genuine rich Ramsey arrow,
selected rich original-partial HE q:D→P into the EXACT first-stage
covered decoder P and internal B coverage, and a genuine ORIGINAL
first-stage selected HE p:P→C0, compose p∘q.

The only small-local input is the first-stage OLD H completion on
EVERY exact n-small vertex set S of the ACTUAL first tagged witness:
one protected map f_S:C.induce(S)→tag(H_S), where H_S is a genuine
transversal partial H-member. For a closed T⊆D with |T|≤n, take
S=q[T] exactly; |S|≤|T|, and no closure hull is generated.

The rich SAME-selected-target bridge (#734) proves an original
partial HE from the full closed T into this very H_S, and hence the
true intrinsic local-completion axiom supplies ONE global H
completion of D. The independent color-transfer proof (#735)
then proves a full original genuine rich Ramsey arrow in that H
member, since A and B are rich irreducible.

This is CONDITIONAL on the EXACT class-local axiom and existence of
the first-stage tagged H witnesses and control. It does NOT prove
the initial two-pass H-class/legal-admissibility bridge nor convert
the printed survey's stronger total-fibre global map to source-defined.
No arbitrary reducible-root gluing is assumed; frozen text unchanged.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure.TrackECanonicalArrowEquivalence

universe u v w
variable {L : Language.{u}}

/-- The genuine partial class may vary with the finite vertex carrier.
This is a class predicate, not an additional homomorphism condition. -/
def HasRichOptionCompletion
    (H : ∀ (Y : Type v), PartialSetStructure L Y → Prop)
    {X : Type v} (D : PartialSetStructure L X) : Prop :=
  ∃ (Y : Type v) (_ : Finite Y)
    (Target : PartialSetStructure L Y),
      H Y Target ∧ ∃ (f : X → Y),
        D.IsOptionClosedFreeHomomorphismEmbedding Target f

/-- Original intrinsic local completion at the fixed B, C0, n.
Every source that has (i) an ORIGINAL source-defined partial HE
to C0, (ii) INTERNAL full B-cover on each genuine rich irreducible
test, and (iii) genuine H-completions of every closed ≤n-vertex
full test receives one global genuine rich H-completion.

The class H is parametrized by exact carriers and may subsequently
be required to be isomorphism closed. Nothing here asserts the
predicate itself for arbitrary H. -/
def RichIntrinsicLocalCompletionAt
    (H : ∀ (Y : Type v), PartialSetStructure L Y → Prop)
    {VB VC : Type v}
    (B : PartialSetStructure L VB)
    (C0 : PartialSetStructure L VC)
    (n : ℕ) : Prop :=
  ∀ (X : Type v) [Finite X] (D : PartialSetStructure L X),
    (∃ (p : X → VC),
      D.IsOptionClosedFreeHomomorphismEmbedding C0 p) →
    (∀ {ECarrier : Type v} (E : PartialSetStructure L ECarrier),
      E.IsOptionClosedFreeIrreducible →
      ∀ e : Embedding E D,
        ∃ j : Embedding B D,
          ∀ x : ECarrier, ∃ b : VB, e.toFun x = j.toFun b) →
    (∀ (T : Finset X), T.card ≤ n →
      ∀ (hT : D.IsClosed (↑T : Set X)),
        HasRichOptionCompletion H
          (D.induceClosed (↑T : Set X) hT)) →
    HasRichOptionCompletion H D

/-- Exact rich class Ramsey consequence of one ACTUAL second witness,
using the first-stage OLD small H completions and ORIGINAL intrinsic
class-local axiom at the SAME fixed n.

The selected H_T map on each small T is *constructed*, not assumed:
take the OLD completion f_S for literal S=q[T], then apply the
SAME-target rich Option(Set) HE proof. Final Ramsey transfer uses
only full A/B copies, never a global full embedding of D. -/
theorem richRamsey_of_intrinsicLocalAndExactOldWitness
    {Parts : Type w} [Fintype Parts]
    {VA VB VX V Q VC : Type v}
    (A : PartialSetStructure L VA)
    (B : PartialSetStructure L VB)
    (D : PartialSetStructure L VX) [Finite VX]
    (C0 : PartialSetStructure L VC)
    (H : ∀ (Y : Type v), PartialSetStructure L Y → Prop)
    (κ : Type*)
    (hA : A.IsOptionClosedFreeIrreducible)
    (hB : B.IsOptionClosedFreeIrreducible)
    (hDArrow : GenuinePartialArrow A B D κ)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (q : VX → V)
    (hq : D.IsOptionClosedFreeHomomorphismEmbedding
      (wholeMaskOriginalDecode C) q)
    (p : V → VC)
    (hp : (wholeMaskOriginalDecode C)
      .IsOptionClosedFreeHomomorphismEmbedding C0 p)
    (hInternalB :
      ∀ {ECarrier : Type v} (E : PartialSetStructure L ECarrier),
        E.IsOptionClosedFreeIrreducible →
        ∀ e : Embedding E D,
          ∃ j : Embedding B D,
            ∀ x : ECarrier, ∃ b : VB, e.toFun x = j.toFun b)
    (n : ℕ)
    (hOldSmall :
      ∀ (S : Set V),
        (∃ (SFin : Finset V),
          S = (↑SFin : Set V) ∧ SFin.card ≤ n) →
        ∃ (Y : Type v) (_ : Finite Y)
          (Target : PartialSetStructure L Y),
          H Y Target ∧
          ∃ (targetPart : Y → Parts),
            FibreTransversal Target targetPart ∧
            ∃ (f : S → Y),
              IsClosedUHomomorphismEmbedding
                ((L.withParts Parts).wholeMaskClosureRules Parts)
                (C.induce S)
                (wholeMaskTagExpansion
                  (withPartsWholeMaskOld Target targetPart)) f)
    (hLocal : RichIntrinsicLocalCompletionAt H B C0 n) :
    ∃ (Y : Type v) (_ : Finite Y) (Target : PartialSetStructure L Y),
      H Y Target ∧ GenuinePartialArrow A B Target κ := by
  classical
  let partD : VX → Parts :=
    fun x => wholeMaskCoveredPart C Base basePart hC hCover (q x)
  have hParts :
      ∀ x : VX,
        wholeMaskCoveredPart C Base basePart hC hCover (q x) = partD x :=
    fun _ => rfl
  have hSmallImage
      (T : Finset VX) (hCard : T.card ≤ n) :
      ∃ (SFin : Finset V),
        (q '' (↑T : Set VX)) = (↑SFin : Set V) ∧
        SFin.card ≤ n := by
    refine ⟨T.image q, ?_, (Finset.card_image_le).trans hCard⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, rfl⟩
  have hSmall :
      ∀ (T : Finset VX), T.card ≤ n →
        ∀ (hT : D.IsClosed (↑T : Set VX)),
          HasRichOptionCompletion H
            (D.induceClosed (↑T : Set VX) hT) := by
    intro T hCard hT
    let S : Set V := q '' (↑T : Set VX)
    obtain ⟨Y, hY, Target, hHY, targetPart, hTrans, f, hf⟩ :=
      hOldSmall S (hSmallImage T hCard)
    letI : Finite Y := hY
    obtain ⟨hSelectedHE, _hSelectedParts⟩ :=
      wholeMaskCovered_selectedRichHEOnClosedT
        C Base basePart hC hPos hCover
        D partD q hq hParts
        (↑T : Set VX) hT Target targetPart hTrans f hf
    exact ⟨Y, hY, Target, hHY,
      f ∘ richExactImageMap q (↑T : Set VX), hSelectedHE⟩
  have hSelectedControl :
      ∃ pTotal : VX → VC,
        D.IsOptionClosedFreeHomomorphismEmbedding C0 pTotal :=
    ⟨p ∘ q, hp.comp hq⟩
  obtain ⟨Y, hY, Target, hHY, fFinal, hFinalHE⟩ :=
    hLocal VX D hSelectedControl hInternalB hSmall
  refine ⟨Y, hY, Target, hHY, ?_⟩
  exact GenuinePartialArrow.of_irreducible_originalPartialHE
    A B D Target κ hA hB hDArrow fFinal hFinalHE

end StructuralRamsey.PartialSetStructure
