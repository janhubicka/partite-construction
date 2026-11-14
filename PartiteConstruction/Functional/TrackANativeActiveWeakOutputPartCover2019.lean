import PartiteConstruction.Functional.TrackAActiveProjectedFibreCover2019
import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019

/-!
# Track A: native active-output-part closure on a true functional partite System

The general exact projected weak-map condition is active-fibre coverage:
every target output label still present among the projected source test
must occur in the surviving output set of the SAME source function input.

In a genuine functional partite System, every complete function fibre is
transversal: two distinct output vertices cannot have the same part.
Therefore the active-fibre coverage condition is equivalent to a much
simpler, pointwise requirement on the actual part map:

For each input tuple x in the exact weak carrier S whose ambient output
fibre Q meets S, every output vertex y in Q whose part label is occupied
somewhere in S MUST itself belong to S.

This is only ACTIVE output-part closure, not global part saturation.
It imposes no condition on unrelated vertices in the same occupied
part, nor on a function input whose entire fibre escapes the test.

Part saturation remains a sufficient condition and in particular holds
for the actual selected supports of embedded control copies. These
results do not construct any local K-completion or a strict functional
mixed-root B-tree witness.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- Minimal active-output-part preservation property of an exact weak
carrier in a true transversal functional partite System. This does
not require retaining all vertices having an occupied part label. -/
def System.ActiveWeakOutputPartCover
    (B : System L P V) (S : Set V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
    ((B.toStructure.func F (Subtype.val ∘ xs)) ∩ S).Nonempty →
    ∀ y : V, y ∈ B.toStructure.func F (Subtype.val ∘ xs) →
      B.part y ∈ B.part '' S → y ∈ S

/-- For an actual functionally transversal partite System, the general
active projected fibre-cover criterion is EXACTLY the native
active-output-part criterion. We use transversality for the forward
direction: another output with the same occupied part must be equal. -/
theorem System.activeWeakOutputPartCover_iff_activeProjectedFibreCover
    (B : System L P V) (S : Set V) :
    B.ActiveWeakOutputPartCover S ↔
      ActiveProjectedFibreCover
        B.toStructure.toNonemptyPartial B.part S := by
  classical
  constructor
  · intro hLocal F xs Q hQ hMeet y hy hyPart
    have hQEq : Q = B.toStructure.func F (Subtype.val ∘ xs) := by
      change (if (B.toStructure.func F (Subtype.val ∘ xs)).Nonempty then
        some (B.toStructure.func F (Subtype.val ∘ xs)) else none) =
          some Q at hQ
      by_cases hNon : (B.toStructure.func F (Subtype.val ∘ xs)).Nonempty
      · simp only [if_pos hNon] at hQ
        exact (Option.some.inj hQ).symm
      · simp only [if_neg hNon] at hQ
        cases hQ
    have hMeetNative :
        ((B.toStructure.func F (Subtype.val ∘ xs)) ∩ S).Nonempty := by
      simpa only [hQEq] using hMeet
    have hyNative :
        y ∈ B.toStructure.func F (Subtype.val ∘ xs) := by
      simpa only [hQEq] using hy
    exact ⟨y, hy, hLocal F xs hMeetNative y hyNative hyPart, rfl⟩
  · intro hCover F xs hMeet y hy hyPart
    have hNonempty :
        (B.toStructure.func F (Subtype.val ∘ xs)).Nonempty := by
      obtain ⟨z, hz, _⟩ := hMeet
      exact ⟨z, hz⟩
    have hVal :
        B.toStructure.toNonemptyPartial.func F (Subtype.val ∘ xs) =
          some (B.toStructure.func F (Subtype.val ∘ xs)) := by
      change (if (B.toStructure.func F (Subtype.val ∘ xs)).Nonempty then
        some (B.toStructure.func F (Subtype.val ∘ xs)) else none) =
          some (B.toStructure.func F (Subtype.val ∘ xs))
      simp only [if_pos hNonempty]
    obtain ⟨z, hzQ, hzS, hEq⟩ :=
      hCover F xs (B.toStructure.func F (Subtype.val ∘ xs))
        hVal hMeet y hy hyPart
    have hzy : z = y :=
      B.funcTransversal F (Subtype.val ∘ xs) z y hzQ hy hEq
    exact hzy ▸ hzS

/-- Global part saturation is sufficient for the weaker local
active-output-part condition. -/
theorem System.PartSaturated.activeWeakOutputPartCover
    (B : System L P V) (S : Set V)
    (hSat : B.PartSaturated S) :
    B.ActiveWeakOutputPartCover S := by
  intro F xs hMeet y hy hyPart
  exact hSat y hyPart

/-- The actual selected support of any embedded control copy
satisfies active-output-part cover, on precisely its original
vertex set and without a generated closure hull. -/
theorem System.support_activeWeakOutputPartCover
    (B : System L P V) {Q : Type v} (α : Q ↪ P) :
    B.ActiveWeakOutputPartCover (B.support α) :=
  System.PartSaturated.activeWeakOutputPartCover B (B.support α)
    (B.support_partSaturated α)


/-- The exact ORIGINAL 2019 source-defined weak projection theorem for
an ACTUAL native transversal functional Picture on any exact carrier
S. It is equivalent to local active output-part closure, not to global
part saturation. This is a same-witness, same-map equivalence. -/
theorem System.arbitraryWeakImage_originalPartial_iff_activePartCover
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D) (S : Set V) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce S)
      (D.weakInduce (B.part '' S))
      (PartialSetStructure.clippedWeakImageMap B.part S) ↔
        B.ActiveWeakOutputPartCover S := by
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part := hB
  have hOrig : Structure.IsOriginalPartialHomomorphism
      B.toStructure D B.part := hp.toOriginalPartial.1
  have hPartial : PartialSetStructure.IsOriginalPartialHomomorphism
      B.toStructure.toNonemptyPartial D.toNonemptyPartial B.part :=
    Structure.TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mp
      hOrig
  have hWeak := hPartial.clippedWeakImage_originalPartial_iff_activeCover S
  rw [← Structure.toNonemptyPartial_weakInduce_commute B.toStructure S,
      ← Structure.toNonemptyPartial_weakInduce_commute D (B.part '' S)]
    at hWeak
  exact (Structure.TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial).trans
    (hWeak.trans
      (B.activeWeakOutputPartCover_iff_activeProjectedFibreCover S).symm)

/-- Regression: the canonical selected support really satisfies the
minimal local criterion, and therefore the existing selected-support
original-partial projection can be recovered via this new iff.
There is NO assertion for all arbitrary weak subsets. -/
theorem System.selectedSupport_originalPartial_via_activePartCover
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {Q : Type v} (α : Q ↪ P) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (B.support α))
      (D.weakInduce (B.part '' B.support α))
      (PartialSetStructure.clippedWeakImageMap B.part (B.support α)) := by
  exact (B.arbitraryWeakImage_originalPartial_iff_activePartCover
    D hB (B.support α)).mpr (B.support_activeWeakOutputPartCover α)

end StructuralRamsey.FunctionalPartite
