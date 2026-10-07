import PartiteConstruction.Functional.EHNPicture
import PartiteConstruction.Functional.EHNStageInvariant

set_option autoImplicit false

/-! # Carrying an auxiliary invariant through one functional Picture step

This is the final bookkeeping layer around the hard local sparsening proof.
For a prescribed placement alpha, preservation of an arbitrary stage predicate
Q reduces to exactly two facts:

* the Hales--Jewett power core satisfies Q;
* adjoining one old-stage copy along the closed support preserves Q.

Finite star attachment and the Picture colouring argument are then automatic.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v

variable {L : Language.{u}}
variable {P U : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Picture Lemma with an auxiliary invariant.

The somewhat explicit `hCore` hypothesis deliberately exposes the exact core
stage constructed by the ordinary functional Picture proof.  This keeps the
future local-tree theorem focused on the geometric core and binary-attachment
lemmas, with no duplicated Ramsey bookkeeping. -/
theorem pictureLemma_preserving
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ]
    (Q : Stage K D → Prop)
    (hCore :
      ∀ (N : ℕ) (hN : 0 < N),
        let R := B.system.weakRestrict D B.isPartite.1 A α
        let hR : R.WeaklyPartiteOver A :=
          B.system.weakRestrict_invariant
            D B.isPartite.1 A α B.isPartite
        let E := Induced.power R N
        let hPower : E.WeaklyPartiteOver A :=
          Induced.power_weaklyPartiteOver hR hN
        let ER := E.relabel α.toFunctionEmbedding
        let hER : ER.WeaklyPartiteOver D :=
          α.isEHNHomomorphismEmbedding.comp hPower
        let T : Stage K D := {
          Carrier := Induced.Vertex R N
          finiteCarrier := inferInstance
          system := ER
          isPartite := hER
          mem := mem_of_weaklyPartiteOver hK E hPower hA
        }
        Q T)
    (hAttach :
      ∀ (T : Stage K D)
        (S : Set B.Carrier)
        (hS : B.system.toStructure.IsClosed S)
        (f : FunctionalPartite.Embedding
          (B.system.induce S hS) T.system),
        Q T →
        Q (T.attach hK B.system B.isPartite B.mem S hS f)) :
    ∃ C : Stage K D,
      Q C ∧ PictureProperty A B C α κ := by
  classical
  let R := B.system.weakRestrict D B.isPartite.1 A α
  have hR : R.WeaklyPartiteOver A :=
    B.system.weakRestrict_invariant
      D B.isPartite.1 A α B.isPartite
  obtain ⟨N, hN, hPower, hArrow⟩ :=
    Induced.weak_partiteLemma_withInvariant hR κ
  let E := Induced.power R N
  have hPower' : E.WeaklyPartiteOver A := by
    simpa [E] using hPower
  have hmE : K E.toStructure :=
    mem_of_weaklyPartiteOver hK E hPower' hA
  let ER := E.relabel α.toFunctionEmbedding
  have hER : ER.WeaklyPartiteOver D :=
    α.isEHNHomomorphismEmbedding.comp hPower'
  let T : Stage K D := {
    Carrier := Induced.Vertex R N
    finiteCarrier := inferInstance
    system := ER
    isPartite := hER
    mem := hmE
  }
  have hQT : Q T := by
    simpa [R, E, ER, T, hR, hPower', hER] using
      hCore N hN
  let S := B.system.support α.toFunctionEmbedding
  have hS : B.system.toStructure.IsClosed S :=
    B.system.weak_support_closed D B.isPartite.1 A α
  let maps : FunctionalPartite.Embedding R E →
      FunctionalPartite.Embedding (B.system.induce S hS) T.system :=
    fun g => {
      toEmbedding := g.toEmbedding
      map_part := fun x =>
        (congrArg α (g.map_part x)).trans
          (B.system.restrictedPart_spec α.toFunctionEmbedding x)
    }
  have hAttach' :
      ∀ (T0 : Stage K D)
        (f0 : FunctionalPartite.Embedding
          (B.system.induce S hS) T0.system),
        Q T0 →
        Q (T0.attach hK B.system B.isPartite B.mem S hS f0) := by
    intro T0 f0 hQT0
    exact hAttach T0 S hS f0 hQT0
  obtain ⟨C, hQC, core, hcopies⟩ :=
    attachAll_preserving
      hK B.system B.isPartite B.mem S hS
      Q hAttach' T hQT maps
  refine ⟨C, hQC, ?_⟩
  intro χ
  obtain ⟨g, hg⟩ := hArrow
    (fun e => χ (core.toEmbedding.comp e.toEmbedding))
  obtain ⟨f, hf⟩ := hcopies g
  refine ⟨f, ?_⟩
  intro e₁ e₂ he₁ he₂
  let r₁ :=
    weakRestrictCopy B.system D B.isPartite.1 A α e₁ he₁
  let r₂ :=
    weakRestrictCopy B.system D B.isPartite.1 A α e₂ he₂
  have hcomp (e : Structure.Embedding A B.system.toStructure)
      (he : ∀ x, B.system.part (e x) = α x) :
      f.toEmbedding.comp e =
        core.toEmbedding.comp
          (g.comp
            (weakRestrictCopy
              B.system D B.isPartite.1 A α e he)).toEmbedding := by
    apply Structure.Embedding.ext
    intro x
    exact hf ⟨e x, x, (he x).symm⟩
  rw [hcomp e₁ he₁, hcomp e₂ he₂]
  exact hg r₁ r₂

end StructuralRamsey.FunctionalPartite.EHN
