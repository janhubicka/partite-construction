import PartiteConstruction.Structure.GenericUFunctionalEquivInto

/-!
# Transfer a functional Ramsey arrow to U-closed relational copies

An arbitrary nonredundant functional target C decodes to a relational
structure. A closed relational map is represented by the SAME carrier map
of a full function embedding, and closed maps compose.

This theorem is an intermediate unoriented arrow-transfer interface.
It does not yet delete/restore the distinguished order symbol or assert the
literal arbitrary-(L,U) ordered result printed in the survey.
-/

namespace StructuralRamsey
namespace RelStructure

universe u v w z
variable {L : RelLanguage.{u}}
variable {V : Type v} {W : Type w} {X : Type z}

theorem IsUClosedEmbedding.comp
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    (f : Embedding B C) (hf : IsUClosedEmbedding B C U hU f)
    (g : Embedding A B) (hg : IsUClosedEmbedding A B U hU g) :
    IsUClosedEmbedding A C U hU (f.comp g) := by
  intro F x y hy
  obtain ⟨z, hz, hfz⟩ := hf F (g.toFun ∘ x) y (by
    simpa [Embedding.comp, Function.comp_assoc] using hy)
  obtain ⟨a, ha, hga⟩ := hg F x z hz
  refine ⟨a, ha, ?_⟩
  calc
    (f.comp g) a = f (g a) := rfl
    _ = f z := congrArg f.toFun hga
    _ = y := hfz

/-- Concrete composition of two U-closed relational embeddings. -/
def uClosedComp
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    (f : {e : Embedding B C // IsUClosedEmbedding B C U hU e})
    (g : {e : Embedding A B // IsUClosedEmbedding A B U hU e}) :
    {e : Embedding A C // IsUClosedEmbedding A C U hU e} :=
  ⟨f.1.comp g.1, IsUClosedEmbedding.comp U hU f.1 f.2 g.1 g.2⟩

@[simp] theorem uClosedComp_apply
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    (f : {e : Embedding B C // IsUClosedEmbedding B C U hU e})
    (g : {e : Embedding A B // IsUClosedEmbedding A B U hU e})
    (a : V) :
    (uClosedComp U hU f g).1 a = f.1 (g.1 a) := rfl

/-- The version of the U-closed Ramsey arrow with a decoded arbitrary
set-valued-function target and *actual relational composition*. -/
def UClosedArrowInto
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X) (κ : Type*) : Prop :=
  ∀ χ : {e : Embedding A (Structure.toRelU U hU C) //
      IsUClosedEmbedding A (Structure.toRelU U hU C) U hU e} → κ,
    ∃ f : {e : Embedding B (Structure.toRelU U hU C) //
      IsUClosedEmbedding B (Structure.toRelU U hU C) U hU e},
      ∀ e₁ e₂ : {e : Embedding A B // IsUClosedEmbedding A B U hU e},
        χ (uClosedComp U hU f e₁) = χ (uClosedComp U hU f e₂)

/-- Transfer monochromatic full-function copies to exactly the
U-closed relational copies of the decoded arbitrary target. -/
theorem uClosedArrowInto_of_functional
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X) (κ : Type*)
    (hRamsey : Structure.Arrow (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU) C κ) :
    UClosedArrowInto A B U hU C κ := by
  let EA := uClosedEmbeddingEquivIntoTarget A U hU C
  let EB := uClosedEmbeddingEquivIntoTarget B U hU C
  intro χ
  let χF : Structure.Embedding (A.asUFunctionsReduced U hU) C → κ :=
    fun e => χ (EA.symm e)
  obtain ⟨f, hf⟩ := hRamsey χF
  refine ⟨EB.symm f, ?_⟩
  intro e₁ e₂
  let e₁F : Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU) :=
    e₁.1.toReducedUFunctions U hU e₁.2
  let e₂F : Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU) :=
    e₂.1.toReducedUFunctions U hU e₂.2
  have hc (e : {g : Embedding A B // IsUClosedEmbedding A B U hU g}) :
      EA.symm (f.comp (e.1.toReducedUFunctions U hU e.2)) =
        uClosedComp U hU (EB.symm f) e := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  have hχ := hf e₁F e₂F
  change χ (EA.symm (f.comp e₁F)) =
    χ (EA.symm (f.comp e₂F)) at hχ
  change χ (uClosedComp U hU (EB.symm f) e₁) =
    χ (uClosedComp U hU (EB.symm f) e₂)
  rw [← hc e₁, ← hc e₂]
  exact hχ

end RelStructure
end StructuralRamsey
