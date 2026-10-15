import PartiteConstruction.Functional.EHNInitialOriginalPartialGeneratorTree
import PartiteConstruction.Functional.EHNInvariantConstruction
import PartiteConstruction.Functional.EHNPictureInvariant
import PartiteConstruction.Functional.EHNNativeOriginalPartialMixedAttachmentReduction
import PartiteConstruction.Functional.EHNNativeOriginalPartialMaximalMixedReduction

/-!
# Published functional n-pass induction reduced to one mixed attachment lemma

The actual Hales--Jewett power core has strict original-partial B-tree
completions at every generator rank. The original initial B-picture
has the same property. Canonicalization and backwards Ramsey colouring
are already verified.

The only unproved input below is rank preservation by one actual
native binary attachment over the closed selected A-support. It must
eventually construct compatible strict B-tree completions of mixed
closed tests with reducible common roots. No Ramsey recursion is replayed.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
noncomputable section

universe u v
variable {L : Language.{u}} {U VB P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The genuine functional Hales--Jewett Picture step raises the strict
original-partial generator-rank invariant as soon as preservation by
the ONE actual native attachment is available. -/
theorem pictureLemma_originalPartial_generatorRank_of_attachment
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] [Finite P] (hKA : K A)
    (Base : Structure L VB) [Finite VB]
    (eAB : Structure.Embedding A Base)
    (Old : Stage K D)
    (alpha : Structure.Embedding A D)
    (κ : Type*) [Fintype κ]
    (n : ℕ)
    (hOld : LocallyGeneratedOriginalPartialTreeCompletable
      Base Old.system.toStructure n)
    (hAttach :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha))
          T.system),
        LocallyGeneratedOriginalPartialTreeCompletable
          Base T.system.toStructure n →
        LocallyGeneratedOriginalPartialTreeCompletable
          Base (T.attach hK Old.system Old.isPartite Old.mem
            (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha)
            f).system.toStructure n) :
    ∃ C : Stage K D,
      LocallyGeneratedOriginalPartialTreeCompletable
        Base C.system.toStructure n ∧
      PictureProperty A Old C alpha κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    LocallyGeneratedOriginalPartialTreeCompletable
      Base T.system.toStructure n
  have hCore :
      ∀ (N : ℕ) (hN : 0 < N),
        let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
        let hR : R.WeaklyPartiteOver A :=
          Old.system.weakRestrict_invariant
            D Old.isPartite.1 A alpha Old.isPartite
        let E := Induced.power R N
        let hPower : E.WeaklyPartiteOver A :=
          Induced.power_weaklyPartiteOver hR hN
        let ER := E.relabel alpha.toFunctionEmbedding
        let hER : ER.WeaklyPartiteOver D :=
          alpha.isEHNHomomorphismEmbedding.comp hPower
        let T : Stage K D := {
          Carrier := Induced.Vertex R N
          finiteCarrier := inferInstance
          system := ER
          isPartite := hER
          mem := mem_of_weaklyPartiteOver hK E hPower hKA
        }
        Q T := by
    intro N hN
    let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
    have hR : R.WeaklyPartiteOver A :=
      Old.system.weakRestrict_invariant
        D Old.isPartite.1 A alpha Old.isPartite
    have hPower :
        LocallyGeneratedOriginalPartialTreeCompletable
          Base (Induced.power R N).toStructure n :=
      power_originalPartial_generatorRank A R hR Base eAB N hN n
    simpa [Q, FunctionalPartite.System.relabel] using hPower
  have hAttachQ :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha))
          T.system),
        Q T →
        Q (T.attach hK Old.system Old.isPartite Old.mem
          (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed D Old.isPartite.1 A alpha)
          f) := by
    intro T f hT
    exact hAttach T f hT
  exact pictureLemma_preservingSupport hK A hKA Old alpha κ
    Q hCore hAttachQ

/-- One COMPLETE class-preserving native functional EHN Ramsey pass
carries strict original-partial generator rank from n-1 to n
provided the single mixed binary attachment lemma holds.

All initial-picture and Hales--Jewett core steps are discharged;
finite Ramsey canonicalization is reused unchanged. -/
theorem inducedConstruction_originalPartial_generatorRank_of_attachment
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L VB) (D : Structure L P)
    [Finite U] [Finite VB] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ)
    (n : ℕ)
    (hD : LocallyGeneratedOriginalPartialTreeCompletable Base D (n - 1))
    (hAttach :
      ∀ (Old T : Stage K D) (alpha : Structure.Embedding A D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha))
          T.system),
        LocallyGeneratedOriginalPartialTreeCompletable
          Base Old.system.toStructure n →
        LocallyGeneratedOriginalPartialTreeCompletable
          Base T.system.toStructure n →
        LocallyGeneratedOriginalPartialTreeCompletable
          Base (T.attach hK Old.system Old.isPartite Old.mem
            (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha)
            f).system.toStructure n) :
    ∃ C : Stage K D,
      LocallyGeneratedOriginalPartialTreeCompletable
        Base C.system.toStructure n ∧
      Structure.Arrow A Base C.system.toStructure κ := by
  classical
  let Q : Stage K D → Prop := fun T =>
    LocallyGeneratedOriginalPartialTreeCompletable
      Base T.system.toStructure n
  have hInitial :
      ∀ beta0 : Structure.Embedding Base D,
        ∃ S : Stage K D, Q S ∧
          ∀ beta : Structure.Embedding Base D,
            ∃ j : Structure.Embedding Base S.system.toStructure,
              ∀ x, S.system.part (j x) = beta x := by
    intro beta0
    obtain ⟨S, hS, hCopies⟩ :=
      initial_originalPartial_generatorRank
        hK Base hKB hBIrr hPos beta0 n
    exact ⟨S, hS, hCopies⟩
  have hStep :
      ∀ (Old : Stage K D) (alpha : Structure.Embedding A D),
        Q Old →
        ∃ C : Stage K D, Q C ∧ PictureProperty A Old C alpha κ := by
    intro Old alpha hOld
    exact pictureLemma_originalPartial_generatorRank_of_attachment
      hK A hKA Base eAB Old alpha κ n hOld
      (fun T f hT => hAttach Old T alpha f hOld hT)
  exact inducedConstruction_preserving
    A Base D κ hRamsey Q hInitial hStep


/-- Published Appendix A functional n-pass iteration, now reduced
exclusively to the *mixed relative-root extension* property of the
exact native binary attachments. The PURE partite cores and PURE
attached copies, the initial Picture, Hales--Jewett canonicalization,
and final backward Ramsey colouring are all discharged by existing
validated constructions. The pending mathematical obligation is
the stated hMixed, not a second recursive Ramsey argument. -/
theorem inducedConstruction_originalPartial_generatorRank_of_mixed_extensions
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L VB) (D : Structure L P)
    [Finite U] [Finite VB] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ)
    (n : ℕ)
    (hD : LocallyGeneratedOriginalPartialTreeCompletable Base D (n - 1))
    (hMixed :
      ∀ (Old T : Stage K D) (alpha : Structure.Embedding A D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha))
          T.system),
        LocallyGeneratedOriginalPartialTreeCompletable
          Base Old.system.toStructure n →
        LocallyGeneratedOriginalPartialTreeCompletable
          Base T.system.toStructure n →
        Attachment.NativeMixedOriginalPartialRelativeExtension
          Old.system (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed D Old.isPartite.1 A alpha)
          T.system f Base n) :
    ∃ C : Stage K D,
      LocallyGeneratedOriginalPartialTreeCompletable
        Base C.system.toStructure n ∧
      Structure.Arrow A Base C.system.toStructure κ := by
  apply inducedConstruction_originalPartial_generatorRank_of_attachment
    hK A Base D hKA hKB hBIrr hPos eAB κ hRamsey n hD
  intro Old T alpha f hOld hCore
  let S := Old.system.support alpha.toFunctionEmbedding
  let hS := Old.system.weak_support_closed
    D Old.isPartite.1 A alpha
  have hNative :
      LocallyGeneratedOriginalPartialTreeCompletable
        Base (Attachment.UnitAttachD Old.system S hS T.system f).toStructure n :=
    Attachment.nativeAttach_generatorRank_of_mixed_relative_extensions
      Old.system S hS T.system f Base n hCore hOld
      (hMixed Old T alpha f hOld hCore)
  change LocallyGeneratedOriginalPartialTreeCompletable
    Base (Attachment.UnitAttachD Old.system S hS T.system f).toStructure n
  exact hNative



/-- Sharp published two-case reduction for a whole genuine functional
induced Ramsey pass. Besides the already checked base, power core,
pure attachments and small projected-image branch, it requires rooted
relative B-tree extensions ONLY for mixed closed tests whose selected
generating support has exactly n distinct projected A-labels.

This exposes the remaining maximal mixed-root lemma as one concrete
functional attachment obligation, and reuses the entire validated
finite Ramsey canonicalization unchanged. -/
theorem inducedConstruction_originalPartial_generatorRank_of_maximal_mixed
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L VB) (D : Structure L P)
    [Finite U] [Finite VB] [Finite P] [DecidableEq P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible)
    (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A Base D κ)
    (n : ℕ)
    (hD : LocallyGeneratedOriginalPartialTreeCompletable Base D (n - 1))
    (hMaxMixed :
      ∀ (Old T : Stage K D) (alpha : Structure.Embedding A D)
        (f : FunctionalPartite.Embedding
          (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
            (Old.system.weak_support_closed D Old.isPartite.1 A alpha))
          T.system),
        LocallyGeneratedOriginalPartialTreeCompletable
          Base Old.system.toStructure n →
        LocallyGeneratedOriginalPartialTreeCompletable
          Base T.system.toStructure n →
        Attachment.NativeMaximalMixedOriginalPartialRelativeExtension
          Old.system (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed D Old.isPartite.1 A alpha)
          T.system f Base n) :
    ∃ C : Stage K D,
      LocallyGeneratedOriginalPartialTreeCompletable
        Base C.system.toStructure n ∧
      Structure.Arrow A Base C.system.toStructure κ := by
  apply inducedConstruction_originalPartial_generatorRank_of_attachment
    hK A Base D hKA hKB hBIrr hPos eAB κ hRamsey n hD
  intro Old T alpha f hOld hCore
  let S := Old.system.support alpha.toFunctionEmbedding
  let hS := Old.system.weak_support_closed
    D Old.isPartite.1 A alpha
  have hPart :
      (Attachment.UnitAttachD Old.system S hS T.system f).WeaklyPartiteOver D :=
    FunctionalPartite.Attachment.unit_weaklyPartiteOver
      Old.system S hS T.system f D Old.isPartite T.isPartite
  have hNative :
      LocallyGeneratedOriginalPartialTreeCompletable
        Base (Attachment.UnitAttachD Old.system S hS T.system f).toStructure n :=
    Attachment.nativeAttach_generatorRank_of_maximal_mixed_extensions
      Old.system S hS T.system f D hPart Base n
      hD hCore hOld (hMaxMixed Old T alpha f hOld hCore)
  change LocallyGeneratedOriginalPartialTreeCompletable
    Base (Attachment.UnitAttachD Old.system S hS T.system f).toStructure n
  exact hNative


end
end StructuralRamsey.FunctionalPartite.EHN
