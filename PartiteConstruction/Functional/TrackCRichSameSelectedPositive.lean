import PartiteConstruction.Functional.TrackCRichOptionEHN
import PartiteConstruction.Functional.TrackCOptionFullExactRange
import PartiteConstruction.Functional.WholeMaskCoveredTaggedWeakLocalMap2019
import PartiteConstruction.Ramsey.ClosureClosedMap

/-!
# Track C: positive genuine rich H completion with the SAME selected OLD map

The original source-defined genuinely partial map q:D→P need not
reflect undefined function inputs. The first-stage ACTUAL tagged
witness C has decoder P with genuine independent domain bits.
Fix one exact closed T in D and S=q[T] in P (S need not be closed).
A selected protected OLD completion f:C.induce S→tag(Target)
induces a source-defined genuine partial homomorphism from the
original full D.induceClosed T into the SAME Target, with literal
vertex map x↦f(⟨q(x),x∈T⟩). The composition preserves original
relations, whole defined values including some(empty), and parts.

The proof uses EXACT whole-fibre weak images; it never replaces S
by a closure hull or claims globally full EHN q. It is a positive
half of the one-H-target completion; full E-copies are separate.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q X Y : Type v}

/-- Exact selected map into S=q[T], with no image-hull generation. -/
def richExactImageMap (q : X → V) (T : Set X) :
    T → (q '' T) :=
  fun x => ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩

/-- A genuine original source-defined HE q, and ONE selected protected
OLD weak completion f_S, give a positive original Option(Set)
homomorphism (and part preservation) of the FULL closed T into
that EXACT SAME selected H target, on the map f_S∘q|T.

This holds for arbitrary independent defined-empty inputs; there is
NO NoDefinedEmptyValues assumption. -/
theorem wholeMaskCovered_selectedRichPositiveOnClosedT
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
    (Target : PartialSetStructure L Y) (targetPart : Y → Parts)
    (f : (q '' T) → Y)
    (hf : IsClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (q '' T))
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f) :
    IsOriginalPartialHomomorphism
      (D.induceClosed T hT) Target
      (f ∘ richExactImageMap q T) ∧
    (∀ x : T,
      targetPart ((f ∘ richExactImageMap q T) x) = partD x.1) := by
  classical
  let S : Set V := q '' T
  let qT : T → S := richExactImageMap q T
  have hWeakMap :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce D T)
        (wholeWeakInduce (wholeMaskOriginalDecode C) S)
        qT :=
    hq.1.wholeWeakRestrict T S qT (fun _ => rfl)
  obtain ⟨hLocal, hLocalParts⟩ :=
    wholeMaskOriginalDecode_weak_originalPartial_of_taggedLocalHom
      C Base basePart hC hPos hCover
      S Target targetPart f hf.1
  have hComposed :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce D T) Target (f ∘ qT) :=
    hLocal.comp hWeakMap
  have hClosedHom :
      IsOriginalPartialHomomorphism
        (D.induceClosed T hT) Target (f ∘ qT) := by
    have hEq : D.wholeWeakInduce T = D.induceClosed T hT :=
      wholeWeakInduce_eq_induceClosed_of_isClosed D T hT
    simpa only [hEq] using hComposed
  refine ⟨hClosedHom, ?_⟩
  intro x
  calc
    targetPart ((f ∘ qT) x) =
        wholeMaskCoveredPart C Base basePart hC hCover (q x.1) :=
      hLocalParts (qT x)
    _ = partD x.1 := hqParts x.1

end StructuralRamsey.PartialSetStructure
