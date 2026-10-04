import PartiteConstruction.Functional.EHNInitial
import PartiteConstruction.Functional.EHNPicture

/-! # One functional induced partite pass inside a free-amalgamation class

The input D is an arbitrary full Ramsey witness, not necessarily in the class.
Only A and B belong to the class. Each Picture step preserves class membership
and the weak homomorphism-embedding projection to D. A single finite pass over
full A-placements, followed by backward colour extraction, gives the witness.
-/
namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}} {P U V : Type v}
variable {K : Structure.StructureClass (L := L)} {D : Structure L P}

/-- One finite pass makes colours depend only on the listed A-placements. -/
theorem canonicalize
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (S : Stage K D) (xs : List (Structure.Embedding A D))
    (κ : Type*) [Fintype κ] :
    ∃ T : Stage K D,
      ∀ χ : Structure.Embedding A T.system.toStructure → κ,
        ∃ f : FunctionalPartite.Embedding S.system T.system,
          ∀ α ∈ xs, ∀ e₁ e₂ : Structure.Embedding A S.system.toStructure,
            (∀ x, S.system.part (e₁ x) = α x) →
            (∀ x, S.system.part (e₂ x) = α x) →
            χ (f.toEmbedding.comp e₁) = χ (f.toEmbedding.comp e₂) := by
  induction xs with
  | nil =>
      refine ⟨S, ?_⟩
      intro χ
      exact ⟨FunctionalPartite.Embedding.id S.system,
        fun _ h => (List.not_mem_nil h).elim⟩
  | cons α xs ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨R, hR⟩ := pictureLemma hK A hA T α κ
      refine ⟨R, ?_⟩
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

/-- The EHN class-preserving version of one induced partite construction.
Projection is weak globally and a full embedding on every full irreducible.
All embeddings in the Ramsey arrow are full function embeddings. -/
theorem inducedConstruction
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : K A) (hB : K B) (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : Structure.Arrow A B D κ) :
    ∃ T : Stage K D, Structure.Arrow A B T.system.toStructure κ := by
  classical
  obtain ⟨β₀, _⟩ := hRamsey (fun _ => Classical.choice (inferInstance : Nonempty κ))
  obtain ⟨S, hS⟩ := initial hK B hB hpos β₀
  letI : Fintype (Structure.Embedding A D) := Fintype.ofFinite _
  let xs : List (Structure.Embedding A D) := Finset.univ.toList
  obtain ⟨T, hT⟩ := canonicalize hK A hA S xs κ
  refine ⟨T, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hT χ
  let HasCopy (α : Structure.Embedding A D) : Prop :=
    ∃ e : Structure.Embedding A S.system.toStructure,
      ∀ x, S.system.part (e x) = α x
  let rep (α : Structure.Embedding A D) (h : HasCopy α) :
      Structure.Embedding A S.system.toStructure := Classical.choose h
  have hrep (α : Structure.Embedding A D) (h : HasCopy α) :
      ∀ x, S.system.part (rep α h x) = α x := Classical.choose_spec h
  let θ : Structure.Embedding A D → κ := fun α =>
    if h : HasCopy α then χ (f.toEmbedding.comp (rep α h))
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨β, hβ⟩ := hRamsey θ
  obtain ⟨j, hj⟩ := hS β
  refine ⟨f.toEmbedding.comp j, ?_⟩
  have hcolour (e : Structure.Embedding A B) :
      θ (β.comp e) = χ ((f.toEmbedding.comp j).comp e) := by
    have hp : ∀ x, S.system.part ((j.comp e) x) = (β.comp e) x :=
      fun x => hj (e x)
    have hc : HasCopy (β.comp e) := ⟨j.comp e, hp⟩
    have hm : β.comp e ∈ xs := by simp [xs]
    have hcanon := hf (β.comp e) hm (rep (β.comp e) hc) (j.comp e)
      (hrep (β.comp e) hc) hp
    have ht : θ (β.comp e) = χ (f.toEmbedding.comp (rep (β.comp e) hc)) := by
      simp only [θ, dite_eq_left hc]
    exact ht.trans hcanon
  intro e₁ e₂
  exact (hcolour e₁).symm.trans ((hβ e₁ e₂).trans (hcolour e₂))

end StructuralRamsey.FunctionalPartite.EHN
