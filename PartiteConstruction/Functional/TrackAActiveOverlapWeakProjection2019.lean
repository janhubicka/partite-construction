import PartiteConstruction.Functional.TrackAActiveWeakPartCoverStability2019

/-!
# Track A: original source-defined weak projection on exact overlap roots

The locally minimal active-output-part condition is stable under two
operations used by the original functional Picture construction:
literal intersections of weak supports and inverse-image restrictions
under FULL part-preserving functional copy embeddings.

This file packages those checked source-side closure principles into the
native weak functional projection statements actually needed by the
induction, via the verified exact iff
`System.arbitraryWeakImage_originalPartial_iff_activePartCover`.

The projection is the TRUE native part map on the unchanged exact
vertex carrier; its target is the literal projected image of that
carrier, not a function-closure hull. In particular none of these
results asserts that an arbitrary weak support is active-cover, or
that positive graph projections are automatically strict functional
homomorphism-embeddings. No strict mixed-root B-tree target completion
or ambient class-local completion theorem is claimed.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- If two exact weak supports of the SAME genuine native functional
Picture have valid source-defined weak projections, *as witnessed by
the local active-cover property*, then their literal intersection
also has the correct source-defined weak projection, with no closure
hull or new target part labels. -/
theorem System.intersection_originalPartialWeakProjection
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S T : Set V)
    (hS : B.ActiveWeakOutputPartCover S)
    (hT : B.ActiveWeakOutputPartCover T) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (S ∩ T))
      (D.weakInduce (B.part '' (S ∩ T)))
      (clippedWeakImageMap B.part (S ∩ T)) := by
  apply (B.arbitraryWeakImage_originalPartial_iff_activePartCover
    D hB (S ∩ T)).mpr
  exact System.ActiveWeakOutputPartCover.inter B S T hS hT

/-- A genuine full part-preserving copy embedding e:B↪C pulls an
active-cover target weak support S back to an exact source weak
support with a valid original partial projection to the control D.
The control of B is assumed genuinely EHN/weakly partite; the
embedding e does not need to be a global EHN projection itself. -/
theorem Embedding.preimage_originalPartialWeakProjection
    {B : System L P V} {C : System L P W}
    (e : Embedding B C)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set W)
    (hS : C.ActiveWeakOutputPartCover S) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (e.toFun ⁻¹' S))
      (D.weakInduce (B.part '' (e.toFun ⁻¹' S)))
      (clippedWeakImageMap B.part (e.toFun ⁻¹' S)) := by
  apply (B.arbitraryWeakImage_originalPartial_iff_activePartCover
    D hB (e.toFun ⁻¹' S)).mpr
  exact e.preimage_activeWeakOutputPartCover S hS

/-- In particular the exact preimage of a canonical selected
control-copy support in C carries an original source-defined weak
projection from the actual smaller System B. -/
theorem Embedding.selectedSupport_preimage_originalPartialWeakProjection
    {B : System L P V} {C : System L P W}
    (e : Embedding B C)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {Q : Type v} (α : Q ↪ P) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (e.toFun ⁻¹' C.support α))
      (D.weakInduce (B.part '' (e.toFun ⁻¹' C.support α)))
      (clippedWeakImageMap B.part (e.toFun ⁻¹' C.support α)) :=
  e.preimage_originalPartialWeakProjection
    D hB (C.support α) (C.support_activeWeakOutputPartCover α)

end StructuralRamsey.FunctionalPartite
