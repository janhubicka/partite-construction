import PartiteConstruction.Functional.TrackCRichSameSelectedFullTarget
import PartiteConstruction.Functional.TrackCRichSameSelectedPositive

/-!
# Track C: the ONE selected H-map is a rich partial HE on the ENTIRE closed T

The full genuinely partial 2019 local-completion condition is not
two unrelated existential statements:
  * source-defined positivity D|T→H_T;
  * full E→H_E for every irreducible E⊆T.
The target H and underlying map must be the SAME for every E.

Take the ACTUAL corrected first-stage B-covered U-closed tagged C,
with genuinely partial original decoder P. Let q:D→P be the selected
original source-defined rich HE from a second loose B-cover. For a
closed exact T⊆D set S=q[T] (possibly NONCLOSED in P) and choose the
SINGLE selected protected OLD weak completion f_S:C.induce(S)→tag(H).

The checked weak-source map semantics (same-map positive proof #733)
gives an original Option(Set) partial homomorphism on D.induceClosed T,
literal map f_S∘q. The actual rich exact U-test/full-target proof
(#732, stacked on #730/#726/#723 and rich adapter #715) shows that
the VERY SAME map is FULL on every genuinely rich irreducible copy
E↪D.induceClosed T, including some(empty) inputs.

Thus ONE H and ONE f_S∘q|T satisfy BOTH parts of the original
genuine-partial homomorphism-embedding definition simultaneously.
No image hull, rank increase, replacement closed source or global
fullness/domain reflection of q. The n-vertex cutoff is used only
to choose f_S for S=q[T] with |S|≤|T|≤n.
The first-stage H-membership and the final intrinsic class-local
application are separate hypotheses/theorems, not proved here.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q X Y : Type v}

/-- The SAME selected OLD tagged H-completion of exact S=q[T]
produces an ORIGINAL source-defined genuinely partial
homomorphism-embedding on the ENTIRE full closed source T,
protecting all its domain-aware irreducible E-copies on
precisely the composite f_S∘q|T vertex map.

Undefined inputs are not globally reflected, but full original
embeddings on every irreducible E DO reflect their domain bits,
including some(empty). The target H is never changed. -/
theorem wholeMaskCovered_selectedRichHEOnClosedT
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
    (D : PartialSetStructure L X)
    (partD : X → Parts)
    (q : X → V)
    (hq : D.IsOptionClosedFreeHomomorphismEmbedding
      (wholeMaskOriginalDecode C) q)
    (hqParts : ∀ x : X,
      wholeMaskCoveredPart C Base basePart hC hCover (q x) = partD x)
    (T : Set X) (hT : D.IsClosed T)
    (Target : PartialSetStructure L Y) [Finite Y]
    (targetPart : Y → Parts)
    (hTrans : FibreTransversal Target targetPart)
    (f : (q '' T) → Y)
    (hf : IsClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (q '' T))
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f) :
    (D.induceClosed T hT).IsOptionClosedFreeHomomorphismEmbedding
      Target (f ∘ richExactImageMap q T) ∧
    (∀ x : T,
      targetPart ((f ∘ richExactImageMap q T) x) = partD x.1) := by
  classical
  obtain ⟨hPositive, hParts⟩ :=
    wholeMaskCovered_selectedRichPositiveOnClosedT
      C Base basePart hC hPos hCover D partD q hq hqParts
      T hT Target targetPart f hf
  refine ⟨⟨hPositive, ?_⟩, hParts⟩
  intro ECarrier E hE e
  let eWhole : Embedding E D :=
    (closedInclusion D T hT).comp e
  have hImageS :
      ∀ z : ECarrier, q (eWhole.toFun z) ∈ (q '' T) := by
    intro z
    exact ⟨(e.toFun z).1, (e.toFun z).2, rfl⟩
  obtain ⟨k, hk⟩ :=
    wholeMaskCovered_selectedRichFullTest_to_sameTarget
      C Base basePart hC hPos hCover
      D q hq (q '' T) Target targetPart hTrans
      f hf E hE eWhole hImageS
  refine ⟨k, ?_⟩
  intro z
  calc
    k.toFun z = f ⟨q (eWhole.toFun z), hImageS z⟩ :=
      hk z
    _ = (f ∘ richExactImageMap q T) (e.toFun z) := by
      apply congrArg f
      apply Subtype.ext
      rfl

end StructuralRamsey.PartialSetStructure
