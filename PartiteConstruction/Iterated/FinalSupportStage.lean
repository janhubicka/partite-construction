import PartiteConstruction.Iterated.FinalSupport
import PartiteConstruction.Iterated.UniformAttachmentBound
import PartiteConstruction.Iterated.AttachmentProjection
import PartiteConstruction.Iterated.AttachmentLocalization

/-! # One uniform final-completion support stage

All original irreducible roots whose chosen image in Base has the same finite
support T are attached simultaneously.  This consumes one fixed-support local
tree budget, independent of how many such roots exist.

The stage keeps the embedding of the original core, the projection to the old
Ramsey witness, the local-tree invariant, and core-or-base localization.
-/
namespace StructuralRamsey.RelStructure.UniformFinal

open Attachment
open FinalSupport
open FinalCompletion

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB O Y : Type v}
variable (Control : RelStructure L UA)
variable (Base : RelStructure L VB)
variable (Orig : RelStructure L O)
variable (Q : RelStructure L Y)
variable (pOrig : O → Y)

/-- State at a specified local-tree size bound. -/
structure Stage (m : ℕ) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  C : RelStructure L Vertex
  core : Embedding Orig C
  projection : Vertex → Y
  projectionHE : C.IsHomomorphismEmbedding Q projection
  core_projection : ∀ o : O, projection (core o) = pOrig o
  locallyTreeLike : LocallyTreeLike Control Base C m
  localized : CoreOrBase (Orig := Orig) (Base := Base) core

attribute [instance] Stage.finiteVertex

/-- Coverage of every original root in one support class. -/
def CoversSupport
    [Fintype O]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    {m : ℕ}
    (S0 : Stage Control Base Orig Q pOrig m)
    (T : Finset VB) : Prop :=
  ∀ r : FinalSupport.AtSupport Orig Base Q pOrig hpOrig hProjected T,
    ∃ beta : Embedding Base S0.C,
      ∀ z : ↥(↑r.1.1 : Set O),
        S0.core z.1 =
          beta (FinalSupport.Root.toBase
            Orig Base Q pOrig hpOrig hProjected r.1 z)

/-- Initial state at any available local-tree level. -/
def initial
    [Finite O]
    {m : ℕ}
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hLTL : LocallyTreeLike Control Base Orig m) :
    Stage Control Base Orig Q pOrig m where
  Vertex := O
  finiteVertex := inferInstance
  C := Orig
  core := Embedding.id Orig
  projection := pOrig
  projectionHE := hpOrig
  core_projection := fun _ => rfl
  locallyTreeLike := hLTL
  localized := coreOrBase_id

/-- Process one support class.  Empty support classes are skipped; otherwise
all roots in the class are attached in one simultaneous attachment. -/
theorem attachSupport
    [Fintype UA] [Fintype VB] [Fintype O]
    (hControl : Control.Irreducible)
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    (T : Finset VB)
    (n : ℕ)
    (S0 :
      Stage Control Base Orig Q pOrig
        (LocallyTreeLike.fixedSupportBudget UA VB n)) :
    ∃ S1 : Stage Control Base Orig Q pOrig n,
      ∃ e : Embedding S0.C S1.C,
        (∀ x : S0.Vertex, S1.projection (e x) = S0.projection x) ∧
        S1.core = e.comp S0.core ∧
        CoversSupport Control Base Orig Q pOrig hpOrig hProjected S1 T := by
  classical
  let I :=
    FinalSupport.AtSupport Orig Base Q pOrig hpOrig hProjected T
  letI : Finite (FinalSupport.Root Orig) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (FinalSupport.Root Orig) := Fintype.ofFinite _
  letI : Finite I :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype I := Fintype.ofFinite I
  by_cases hI : Nonempty I
  · let r0 : I := Classical.choice hI
    have hRoot :
        (Base.induce (↑T : Set VB)).Irreducible := by
      have h :=
        FinalSupport.Root.support_irreducible
          Orig Base Q pOrig hpOrig hProjected r0.1
      rw [r0.2] at h
      exact h
    let fGroup : I → Embedding (Base.induce (↑T : Set VB)) S0.C :=
      fun r =>
        S0.core.comp
          (FinalSupport.AtSupport.embedding
            Orig Base Q pOrig hpOrig hProjected T r)
    let pCopy : I → Embedding Base Q :=
      fun r =>
        FinalSupport.Root.beta Orig Base Q pOrig hProjected r.1
    have hcompat :
        ∀ r : I, ∀ x : ↥(↑T : Set VB),
          S0.projection (fGroup r x) = pCopy r x.1 := by
      intro r x
      calc
        S0.projection (fGroup r x) =
            pOrig
              (FinalSupport.AtSupport.embedding
                Orig Base Q pOrig hpOrig hProjected T r x) :=
          S0.core_projection _
        _ = pCopy r x.1 :=
          FinalSupport.AtSupport.embedding_compat
            Orig Base Q pOrig hpOrig hProjected T r x
    let C1 := Attachment.attach Base (↑T : Set VB) S0.C fGroup
    let e : Embedding S0.C C1 :=
      Attachment.coreEmbedding Base (↑T : Set VB) S0.C fGroup
    let p1 : Attachment.Vertex (↑T : Set VB) → Y :=
      Attachment.fold S0.projection (fun r => pCopy r)
    have hp1 : C1.IsHomomorphismEmbedding Q p1 :=
      Attachment.fold_isHomomorphismEmbedding
        S0.projection pCopy hcompat S0.projectionHE
    have hLTL :
        LocallyTreeLike Control Base C1 n :=
      LocallyTreeLike.attachment_locallyTreeLike_fixedSupport
        (Control := Control) (Base := Base) (Core := S0.C)
        (S := (↑T : Set VB)) (f := fGroup)
        hControl hRoot n S0.locallyTreeLike
    let core1 : Embedding Orig C1 := e.comp S0.core
    let S1 : Stage Control Base Orig Q pOrig n := {
      Vertex := Attachment.Vertex (↑T : Set VB)
      finiteVertex := inferInstance
      C := C1
      core := core1
      projection := p1
      projectionHE := hp1
      core_projection := by
        intro o
        change
          Attachment.fold S0.projection (fun r => pCopy r)
            (Sum.inl (S0.core o)) = pOrig o
        exact S0.core_projection o
      locallyTreeLike := hLTL
      localized :=
        FinalCompletion.coreOrBase_attachment
          (Orig := Orig) (Base := Base)
          (Current := S0.C) (S := (↑T : Set VB)) (f := fGroup)
          S0.localized
    }
    refine ⟨S1, e, ?_, rfl, ?_⟩
    · intro x
      rfl
    · intro r
      let betar : Embedding Base S1.C :=
        Attachment.copyEmbedding Base (↑T : Set VB) S0.C fGroup r
      refine ⟨betar, ?_⟩
      intro z
      let eRB :=
        FinalSupport.Root.toBase
          Orig Base Q pOrig hpOrig hProjected r.1
      have hbSupport :
          eRB z ∈
            FinalSupport.Root.support
              Orig Base Q pOrig hpOrig hProjected r.1 := by
        exact
          (eRB.mem_imageFinset_iff (eRB z)).mpr ⟨z, rfl⟩
      have hbT : eRB z ∈ T := by
        exact
          Eq.mp
            (congrArg (fun U : Finset VB => eRB z ∈ U) r.2)
            hbSupport
      let x : ↥(↑T : Set VB) := ⟨eRB z, hbT⟩
      have hinv :
          Embedding.imageInverseAt eRB T r.2 x = z := by
        apply eRB.injective
        calc
          eRB (Embedding.imageInverseAt eRB T r.2 x) = x.1 :=
            Embedding.imageInverseAt_apply eRB T r.2 x
          _ = eRB z := rfl
      have hback :
          FinalSupport.AtSupport.embedding
              Orig Base Q pOrig hpOrig hProjected T r x =
            z.1 := by
        change
          (Embedding.imageInverseAt eRB T r.2 x).1 = z.1
        exact congrArg Subtype.val hinv
      change core1 z.1 = betar (eRB z)
      calc
        core1 z.1 = e (S0.core z.1) := rfl
        _ = e (fGroup r x) := by
          apply congrArg e
          change S0.core z.1 =
            S0.core
              (FinalSupport.AtSupport.embedding
                Orig Base Q pOrig hpOrig hProjected T r x)
          exact congrArg S0.core hback.symm
        _ = betar x.1 := by
          exact
            (Attachment.copy_extends
              Base (↑T : Set VB) S0.C fGroup r x).symm
        _ = betar (eRB z) := rfl
  · letI : IsEmpty I := ⟨fun r => hI ⟨r⟩⟩
    have hmono :
        LocallyTreeLike Control Base S0.C n := by
      apply S0.locallyTreeLike.mono
      simp [LocallyTreeLike.fixedSupportBudget]
    let S1 : Stage Control Base Orig Q pOrig n := {
      Vertex := S0.Vertex
      finiteVertex := inferInstance
      C := S0.C
      core := S0.core
      projection := S0.projection
      projectionHE := S0.projectionHE
      core_projection := S0.core_projection
      locallyTreeLike := hmono
      localized := S0.localized
    }
    refine ⟨S1, Embedding.id S0.C, ?_, ?_, ?_⟩
    · intro x
      rfl
    · ext o
      rfl
    · intro r
      exact isEmptyElim r

end StructuralRamsey.RelStructure.UniformFinal
