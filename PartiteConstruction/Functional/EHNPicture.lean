import PartiteConstruction.Functional.EHNStage

set_option autoImplicit false

/-! # One class-preserving functional Picture step

The power belongs to the class because every full irreducible embeds into A.
Copies of the old stage are then attached along closed supports. All embeddings
used by the colouring argument are full, even though projections are weak.
-/
namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P U : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- Canonicality at a prescribed full A-placement. -/
def PictureProperty
    (A : Structure L U) (B C : Stage K D)
    (α : Structure.Embedding A D) (κ : Type*) : Prop :=
  ∀ χ : Structure.Embedding A C.system.toStructure → κ,
    ∃ f : FunctionalPartite.Embedding B.system C.system,
      ∀ e₁ e₂ : Structure.Embedding A B.system.toStructure,
        (∀ x, B.system.part (e₁ x) = α x) →
        (∀ x, B.system.part (e₂ x) = α x) →
        χ (f.toEmbedding.comp e₁) = χ (f.toEmbedding.comp e₂)

/-- Functional Picture Lemma inside a hereditary free-amalgamation class. -/
theorem pictureLemma
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D, PictureProperty A B C α κ := by
  classical
  let R := B.system.weakRestrict D B.isPartite.1 A α
  have hR : R.WeaklyPartiteOver A :=
    B.system.weakRestrict_invariant D B.isPartite.1 A α B.isPartite
  obtain ⟨N, hN, hPower, hArrow⟩ :=
    Induced.weak_partiteLemma_withInvariant hR κ
  let E := Induced.power R N
  have hmE : K E.toStructure := mem_of_weaklyPartiteOver hK E hPower hA
  let ER := E.relabel α.toFunctionEmbedding
  have hER : ER.WeaklyPartiteOver D :=
    α.isEHNHomomorphismEmbedding.comp hPower
  let T : Stage K D := {
    Carrier := Induced.Vertex R N
    finiteCarrier := inferInstance
    system := ER
    isPartite := hER
    mem := hmE
  }
  let S := B.system.support α.toFunctionEmbedding
  have hS : B.system.toStructure.IsClosed S :=
    B.system.weak_support_closed D B.isPartite.1 A α
  let maps : FunctionalPartite.Embedding R E →
      FunctionalPartite.Embedding (B.system.induce S hS) T.system := fun g => {
    toEmbedding := g.toEmbedding
    map_part := fun x => (congrArg α (g.map_part x)).trans
      (B.system.restrictedPart_spec α.toFunctionEmbedding x)
  }
  obtain ⟨C, core, hcopies⟩ := attachAll hK B.system B.isPartite B.mem S hS T maps
  refine ⟨C, ?_⟩
  intro χ
  obtain ⟨g, hg⟩ := hArrow
    (fun e => χ (core.toEmbedding.comp e.toEmbedding))
  obtain ⟨f, hf⟩ := hcopies g
  refine ⟨f, ?_⟩
  intro e₁ e₂ he₁ he₂
  let r₁ := weakRestrictCopy B.system D B.isPartite.1 A α e₁ he₁
  let r₂ := weakRestrictCopy B.system D B.isPartite.1 A α e₂ he₂
  have hcomp (e : Structure.Embedding A B.system.toStructure)
      (he : ∀ x, B.system.part (e x) = α x) :
      f.toEmbedding.comp e = core.toEmbedding.comp
        (g.comp (weakRestrictCopy B.system D B.isPartite.1 A α e he)).toEmbedding := by
    apply Structure.Embedding.ext
    intro x
    exact hf ⟨e x, x, (he x).symm⟩
  rw [hcomp e₁ he₁, hcomp e₂ he₂]
  exact hg r₁ r₂

end StructuralRamsey.FunctionalPartite.EHN
