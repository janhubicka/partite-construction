import PartiteConstruction.Functional.EHNConstruction

set_option autoImplicit false

/-! # Carrying auxiliary invariants through one functional EHN pass

The hard functional sparsening work is local to one Picture transition.  Once
an auxiliary predicate on EHN stages is known to survive the initial picture
and every prescribed Picture step, the ordinary finite canonicalization and
backward colour extraction carry it through the whole induced construction.

This file packages that bookkeeping independently of the particular invariant.
It is intended for the closed local-tree/history invariant: after the binary
mixed attachment theorem is supplied, no further Ramsey argument is needed.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v

variable {L : Language.{u}}
variable {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Canonicalize a finite list of A-placements while preserving an arbitrary
predicate on EHN stages.

All structural work is delegated to `hStep`: for one prescribed placement it
must choose a Picture witness which both has the usual canonicality property
and preserves `Q`. -/
theorem canonicalize_preserving
    (A : Structure L U) [Finite U]
    (κ : Type*) [Fintype κ]
    (Q : Stage K D → Prop)
    (hStep :
      ∀ (S : Stage K D) (α : Structure.Embedding A D),
        Q S →
        ∃ R : Stage K D,
          Q R ∧ PictureProperty A S R α κ)
    (S : Stage K D) (hQS : Q S)
    (xs : List (Structure.Embedding A D)) :
    ∃ T : Stage K D,
      Q T ∧
      ∀ χ : Structure.Embedding A T.system.toStructure → κ,
        ∃ f : FunctionalPartite.Embedding S.system T.system,
          ∀ α ∈ xs, ∀ e₁ e₂ : Structure.Embedding A S.system.toStructure,
            (∀ x, S.system.part (e₁ x) = α x) →
            (∀ x, S.system.part (e₂ x) = α x) →
            χ (f.toEmbedding.comp e₁) =
              χ (f.toEmbedding.comp e₂) := by
  induction xs with
  | nil =>
      refine ⟨S, hQS, ?_⟩
      intro χ
      exact ⟨FunctionalPartite.Embedding.id S.system,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons α xs ih =>
      obtain ⟨T, hQT, hT⟩ := ih
      obtain ⟨R, hQR, hR⟩ := hStep T α hQT
      refine ⟨R, hQR, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hR χ
      obtain ⟨f, hf⟩ := hT (fun e => χ (g.toEmbedding.comp e))
      refine ⟨g.comp f, ?_⟩
      intro β hβ e₁ e₂ he₁ he₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hg (f.toEmbedding.comp e₁) (f.toEmbedding.comp e₂)
          (fun x => (f.map_part (e₁ x)).trans (he₁ x))
          (fun x => (f.map_part (e₂ x)).trans (he₂ x))
      · exact hf β hβ e₁ e₂ he₁ he₂

/-- Abstract one-pass EHN construction with an auxiliary stage invariant.

The initial-stage hypothesis contains exactly the information used by the
usual EHN proof: every full B-placement in D is represented by a B-copy in the
initial stage.  The step hypothesis is the sole remaining obligation for a
new invariant. -/
theorem inducedConstruction_preserving
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ)
    (Q : Stage K D → Prop)
    (hInitial :
      ∀ β₀ : Embedding B D,
        ∃ S : Stage K D,
          Q S ∧
          ∀ β : Embedding B D,
            ∃ j : Structure.Embedding B S.system.toStructure,
              ∀ x, S.system.part (j x) = β x)
    (hStep :
      ∀ (S : Stage K D) (α : Structure.Embedding A D),
        Q S →
        ∃ R : Stage K D,
          Q R ∧ PictureProperty A S R α κ) :
    ∃ T : Stage K D,
      Q T ∧ Structure.Arrow A B T.system.toStructure κ := by
  classical
  obtain ⟨β₀, _⟩ :=
    hRamsey (fun _ => Classical.choice (inferInstance : Nonempty κ))
  obtain ⟨S, hQS, hCopies⟩ := hInitial β₀
  letI : Fintype (Structure.Embedding A D) := Fintype.ofFinite _
  let xs : List (Structure.Embedding A D) := Finset.univ.toList
  obtain ⟨T, hQT, hT⟩ :=
    canonicalize_preserving A κ Q hStep S hQS xs
  refine ⟨T, hQT, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hT χ
  let HasCopy (α : Structure.Embedding A D) : Prop :=
    ∃ e : Structure.Embedding A S.system.toStructure,
      ∀ x, S.system.part (e x) = α x
  let rep (α : Structure.Embedding A D) (h : HasCopy α) :
      Structure.Embedding A S.system.toStructure :=
    Classical.choose h
  have hrep (α : Structure.Embedding A D) (h : HasCopy α) :
      ∀ x, S.system.part (rep α h x) = α x :=
    Classical.choose_spec h
  let θ : Structure.Embedding A D → κ := fun α =>
    if h : HasCopy α then
      χ (f.toEmbedding.comp (rep α h))
    else
      Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, hβ⟩ := hRamsey θ
  obtain ⟨j, hj⟩ := hCopies β
  refine ⟨f.toEmbedding.comp j, ?_⟩
  have hcolour (e : Structure.Embedding A B) :
      θ (β.comp e) =
        χ ((f.toEmbedding.comp j).comp e) := by
    have hp :
        ∀ x, S.system.part ((j.comp e) x) = (β.comp e) x :=
      fun x => hj (e x)
    have hc : HasCopy (β.comp e) := ⟨j.comp e, hp⟩
    have hm : β.comp e ∈ xs := by
      simp [xs]
    have hcanon :=
      hf (β.comp e) hm (rep (β.comp e) hc) (j.comp e)
        (hrep (β.comp e) hc) hp
    have ht :
        θ (β.comp e) =
          χ (f.toEmbedding.comp (rep (β.comp e) hc)) := by
      simp only [θ, dite_eq_left hc]
    exact ht.trans hcanon
  intro e₁ e₂
  exact
    (hcolour e₁).symm.trans
      ((hβ e₁ e₂).trans (hcolour e₂))

end StructuralRamsey.FunctionalPartite.EHN
