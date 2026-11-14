import PartiteConstruction.Functional.TrackAArbitraryClippedWeakImagePositive2019
import PartiteConstruction.Functional.TrackANativeClippedOriginalPreimage2019
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Track A: exact arbitrary weak-image map interface on the actual native Picture

The earlier Track A Option(Set) theory distinguishes a positive Dom_F/Graph_F
homomorphism from an original source-defined partial-function homomorphism.
This file transfers the exact interface back to the native Structure language
of the Nešetřil-programme survey. Undefined native inputs are empty fibres;
the canonical toNonemptyPartial encoding reflects this convention without
manufacturing defined-empty native values.

On EVERY literal weak subset S of a native original-partial map f:A→B,
the map S→f[S] is a positive domain/output-graph homomorphism, even if S
is not saturated. It is an original source-defined partial homomorphism
exactly when no extra output is present in the projected WEAK target fibre
over any WEAK-defined source input.

For an actual weakly partite functional System B over control D, the part
map meets the hypotheses. The canonical support selected by an embedded
control copy automatically satisfies the no-extra-output condition by the
previously verified part-saturation theorem.

These are same-carrier map statements; there is no hull enlargement,
reflection of undefined inputs, generic local K-completion or strict
history-compatible B-tree construction.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- For an arbitrary exact native clipped weak carrier S, the original
source-defined map f preserves ALL positive Dom_F/Graph_F relations on
the canonical nonempty-fibre partial encodings of the weak structures. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_domainGraphHom
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) (S : Set V) :
    (PartialSetStructure.domainGraph
      ((A.weakInduce S).toNonemptyPartial)).IsHomomorphism
      (PartialSetStructure.domainGraph
        ((B.weakInduce (f '' S)).toNonemptyPartial))
      (PartialSetStructure.clippedWeakImageMap f S) := by
  have hPartial : PartialSetStructure.IsOriginalPartialHomomorphism
      A.toNonemptyPartial B.toNonemptyPartial f :=
    TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mp hf
  have hGraph := hPartial.clippedWeakImage_graphHom S
  rw [← toNonemptyPartial_weakInduce_commute A S,
      ← toNonemptyPartial_weakInduce_commute B (f '' S)] at hGraph
  exact hGraph

/-- Exact criterion for upgrading the ALWAYS-positive native clipped
weak-image map to an original-2019 SOURCE-DEFINED partial homomorphism.
The extra-output condition is tested on the actual weak structures,
not the full ambient fibres or their closure hulls. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_iff_noExtra
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) (S : Set V) :
    IsOriginalPartialHomomorphism
        (A.weakInduce S) (B.weakInduce (f '' S))
        (PartialSetStructure.clippedWeakImageMap f S) ↔
      PartialSetStructure.NoExtraTargetOutputsOnDefined
        ((A.weakInduce S).toNonemptyPartial)
        ((B.weakInduce (f '' S)).toNonemptyPartial)
        (PartialSetStructure.clippedWeakImageMap f S) := by
  have hPartial : PartialSetStructure.IsOriginalPartialHomomorphism
      A.toNonemptyPartial B.toNonemptyPartial f :=
    TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mp hf
  have hIff := hPartial.clippedWeakImage_originalPartial_iff_noExtra S
  rw [← toNonemptyPartial_weakInduce_commute A S,
      ← toNonemptyPartial_weakInduce_commute B (f '' S)] at hIff
  exact TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.trans
    hIff

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- For the actual functional partite System, EVERY exact weak vertex
test has a positive domain/output-graph projection to its occupied
control parts. Neither full source-domain reflection nor global
part-saturation is asserted. -/
theorem System.arbitraryWeakImage_domainGraphHom
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) (S : Set V) :
    (PartialSetStructure.domainGraph
      ((B.toStructure.weakInduce S).toNonemptyPartial)).IsHomomorphism
      (PartialSetStructure.domainGraph
        ((D.weakInduce (B.part '' S)).toNonemptyPartial))
      (PartialSetStructure.clippedWeakImageMap B.part S) := by
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part := hB
  have hOrig : Structure.IsOriginalPartialHomomorphism
      B.toStructure D B.part := hp.toOriginalPartial.1
  exact hOrig.clippedWeakImage_domainGraphHom S

/-- Over arbitrary (possibly NON-saturated) native weak tests, the
precise remaining obstacle to a source-defined functional projection
is the no-extra-target-output property, not an automatic requirement
of global part-saturation. -/
theorem System.arbitraryWeakImage_originalPartial_iff_noExtra
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) (S : Set V) :
    Structure.IsOriginalPartialHomomorphism
        (B.toStructure.weakInduce S)
        (D.weakInduce (B.part '' S))
        (PartialSetStructure.clippedWeakImageMap B.part S) ↔
      PartialSetStructure.NoExtraTargetOutputsOnDefined
        ((B.toStructure.weakInduce S).toNonemptyPartial)
        ((D.weakInduce (B.part '' S)).toNonemptyPartial)
        (PartialSetStructure.clippedWeakImageMap B.part S) := by
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part := hB
  have hOrig : Structure.IsOriginalPartialHomomorphism
      B.toStructure D B.part := hp.toOriginalPartial.1
  exact hOrig.clippedWeakImage_iff_noExtra S

/-- A selected support of an embedded control copy is known to be
part-saturated, so it automatically meets the WEAKER precise
no-extra-output condition. This uses the true native weak partite
Picture and not an abstract replacement by a closure hull. -/
theorem System.selectedSupport_noExtra
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {Q : Type v} (α : Q ↪ P) :
    PartialSetStructure.NoExtraTargetOutputsOnDefined
      ((B.toStructure.weakInduce (B.support α)).toNonemptyPartial)
      ((D.weakInduce (B.part '' B.support α)).toNonemptyPartial)
      (PartialSetStructure.clippedWeakImageMap B.part (B.support α)) := by
  have hIff :=
    B.arbitraryWeakImage_originalPartial_iff_noExtra D hB (B.support α)
  exact hIff.mp (B.support_originalPartial_weakProjection D hB α)

end StructuralRamsey.FunctionalPartite
