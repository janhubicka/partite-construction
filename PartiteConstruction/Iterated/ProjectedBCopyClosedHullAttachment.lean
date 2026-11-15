import PartiteConstruction.Iterated.ProjectedBCopyControlCover
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-!
# Track E: closed-hull projected B attachments preserve U-closedness and control HE

An ordinary irreducible core S need not be U-closed, so freely attaching
a B-copy over S is not enough to preserve the tagged 2019 U-closedness.
The already verified free-amalgam closure theorem requires the COMMON
ROOT itself to be U-closed.

Instead use the ambient U-closure H=cl_U^Orig(S) as a final B-attachment
root, NEVER as a replacement for any small weak Ramsey test. On a U-closed
Orig, H is U-closed and U-irreducible. Protected external coverage
embeds this literal H in hereditarily ordinary-irreducible Base, making H
ordinarily irreducible. The selected homomorphism-embedding into a
Control with INTERNAL B-cover then places the selected image of H inside
a real B-copy beta:Base↪Control. The verified compatible attachment
gives a free amalgam with the SAME selected HE projection on all old
vertices. U-closedness of the amalgam follows from its closed common H.

This is a ONE-STEP interface, not a claim that a finite iteration of
such attachments preserves small H-relative weak completions or the
full canonical 2019 complete-mask decoder.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FreeAmalgam

universe u v
variable {L : RelLanguage.{u}} {O B Q : Type v}

/-- For every ordinary irreducible source seed, the exact ambient
U-closed hull is also an ordinarily irreducible source test, and its
SAME selected control image lies in an actual B-copy of the Control. -/
theorem closedHull_has_selected_controlBCopy
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hOrigClosed : IsUClosed rules Orig)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control)
    (S : Set O) (hSIrred : (Orig.induce S).Irreducible) :
    ∃ (H : Set O),
      S ⊆ H ∧
      IsUClosed rules (Orig.induce H) ∧
      IsUIrreducible rules (Orig.induce H) ∧
      (Orig.induce H).Irreducible ∧
      ∃ beta : Embedding Base Control,
        ∀ z : H, ∃ b : B, pOrig z.1 = beta b := by
  let H : Set O := UClosureHull rules Orig S
  have hHClosed : IsUClosed rules (Orig.induce H) :=
    hOrigClosed.induce_UClosureHull S
  have hHUIrred : IsUIrreducible rules (Orig.induce H) :=
    hOrigClosed.irreducibleSeed_hull_isUIrreducible S hSIrred
  obtain ⟨eB⟩ :=
    hExternal (Orig.induce H) hHClosed hHUIrred
      (inclusion Orig H)
  have hHOrdIrred : (Orig.induce H).Irreducible :=
    hBaseHered.of_embedding eB
  obtain ⟨beta, hBeta⟩ :=
    projected_images_extend_of_control_internalCover
      Orig Base Control pOrig hpOrig hControl H hHOrdIrred
  exact ⟨H, subset_UClosureHull rules Orig S,
    hHClosed, hHUIrred, hHOrdIrred, beta, hBeta⟩

/-- A real B-copy attachment along the U-CLOSED hull of S preserves
the selected SAME control HE as well as the source U-closedness.
The new actual Base-copy is explicitly mapped by beta into Control. -/
theorem attach_closedHull_preserves_UClosed_controlHE
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hOrigClosed : IsUClosed rules Orig)
    (hBaseClosed : IsUClosed rules Base)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control)
    (S : Set O) (hSIrred : (Orig.induce S).Irreducible) :
    ∃ (H : Set O), S ⊆ H ∧
      ∃ beta : Embedding Base Control,
        ∃ j : Embedding (Orig.induce H) Base,
          ∃ newProjection :
            FreeAmalgam.Vertex (Orig.induce H) Orig Base
              (inclusion Orig H) j → Q,
            IsUClosed rules
              (FreeAmalgam.amalgam (Orig.induce H) Orig Base
                (inclusion Orig H) j) ∧
            (FreeAmalgam.amalgam (Orig.induce H) Orig Base
                (inclusion Orig H) j).IsHomomorphismEmbedding
                Control newProjection ∧
            (∀ o : O, newProjection
              (FreeAmalgam.leftEmbedding
                (Orig.induce H) Orig Base (inclusion Orig H) j o) =
                pOrig o) ∧
            (∀ b : B, newProjection
              (FreeAmalgam.rightEmbedding
                (Orig.induce H) Orig Base (inclusion Orig H) j b) =
                beta b) := by
  classical
  obtain ⟨H, hSH, hHClosed, _hHUIrred, hHOrdIrred,
      beta, hBeta⟩ :=
    closedHull_has_selected_controlBCopy
      Orig Base Control pOrig hOrigClosed hExternal
      hBaseHered hpOrig hControl S hSIrred
  let i : Embedding (Orig.induce H) Orig := inclusion Orig H
  obtain ⟨j, newProjection, hProjected, hLeft, hRight, _hOverlap⟩ :=
    attach_irreducible_preserves_controlHE
      hHOrdIrred i pOrig hpOrig beta hBeta
  have hFree : IsFreeAmalgam i j
      (FreeAmalgam.leftEmbedding (Orig.induce H) Orig Base i j)
      (FreeAmalgam.rightEmbedding (Orig.induce H) Orig Base i j) :=
    FreeAmalgam.isFreeAmalgam (Orig.induce H) Orig Base i j
  have hWholeClosed :
      IsUClosed rules
        (FreeAmalgam.amalgam (Orig.induce H) Orig Base i j) :=
    hFree.isUClosed hHClosed hOrigClosed hBaseClosed
  exact ⟨H, hSH, beta, j, newProjection, hWholeClosed,
    hProjected, hLeft, hRight⟩

end StructuralRamsey.RelStructure.ProjectedBCopyControl
