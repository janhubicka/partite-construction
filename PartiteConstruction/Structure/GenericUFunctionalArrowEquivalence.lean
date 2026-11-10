import PartiteConstruction.Structure.GenericUFunctionalArrowTransfer

/-!
# Bidirectional generic U-closed ↔ full-functional Ramsey arrow dictionary

This is deliberately an UNORDERED intermediate theorem; the named order
will be removed from the original relational language in the final wrapper.
Unlike the preliminary redundant-language dictionary, the target C below
is an ARBITRARY structure in the nonredundant reduced language.

Both arrows use actual map composition, so no coloring domain is enlarged.
Original non-U relations, empty function fibres, repeated-coordinate tuples
and original vertex carriers are all preserved.

Candidate source proof. An exact-head Lean build plus #print axioms is needed
before it can be considered machine-checked.
-/

namespace StructuralRamsey
universe u v w z

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}
variable {X : Type z}

/-- Recover the ORIGINAL relational target B, rather than merely its decoded
round trip. This direction handles full embeddings of canonical reduced
encodings; it places no coherence assumptions on arbitrary other targets. -/
def Embedding.fromReducedUFunctions
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (f : Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU)) :
    Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    exact
      (toRelU_asUFunctionsReduced_rel_iff B U hU R (f.toFun ∘ x)).symm.trans
        ((Embedding.fromReducedUFunctionsTarget U hU f).map_rel_iff R x)

/-- A full reduced embedding into a canonical target is genuinely U-closed
as an embedding of the ORIGINAL relational structures. -/
theorem Embedding.fromReducedUFunctions_uClosed
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (f : Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU)) :
    IsUClosedEmbedding A B U hU
      (Embedding.fromReducedUFunctions U hU f) := by
  intro F x y hy
  have hyDecoded :
      (Structure.toRelU U hU (B.asUFunctionsReduced U hU)).rel F.1
        (RelLanguage.appendU L U hU F (f.toFun ∘ x) y) :=
    (toRelU_asUFunctionsReduced_rel_iff B U hU F.1
      (RelLanguage.appendU L U hU F (f.toFun ∘ x) y)).mpr hy
  obtain ⟨z, hz, hzy⟩ :=
    (Embedding.fromReducedUFunctionsTarget_uClosed U hU f)
      F x y hyDecoded
  exact ⟨z, hz, hzy⟩

/-- Full embedding types of two canonical encodings are exactly their
original genuine induced U-closed relational embedding types. -/
def uClosedEmbeddingEquivReduced
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    {e : Embedding A B // IsUClosedEmbedding A B U hU e} ≃
      Structure.Embedding (A.asUFunctionsReduced U hU)
        (B.asUFunctionsReduced U hU) where
  toFun e := e.1.toReducedUFunctions U hU e.2
  invFun f := ⟨Embedding.fromReducedUFunctions U hU f,
    Embedding.fromReducedUFunctions_uClosed U hU f⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Structure.Embedding.ext
    intro x
    rfl

/-- A U-closed relational arrow into the decoded ARBITRARY functional
target implies the corresponding full-functional Ramsey arrow. -/
theorem functionalArrow_of_UClosedArrowInto
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X) (κ : Type*)
    (h : UClosedArrowInto A B U hU C κ) :
    Structure.Arrow (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU) C κ := by
  let EA := uClosedEmbeddingEquivIntoTarget A U hU C
  let EB := uClosedEmbeddingEquivIntoTarget B U hU C
  let EAB := uClosedEmbeddingEquivReduced A B U hU
  intro χ
  let χR : {e : Embedding A (Structure.toRelU U hU C) //
      IsUClosedEmbedding A (Structure.toRelU U hU C) U hU e} → κ :=
    fun e => χ (EA e)
  obtain ⟨fR, hf⟩ := h χR
  refine ⟨EB fR, ?_⟩
  intro e₁ e₂
  have hcomp (e : Structure.Embedding (A.asUFunctionsReduced U hU)
      (B.asUFunctionsReduced U hU)) :
      EA (uClosedComp U hU fR (EAB.symm e)) = (EB fR).comp e := by
    apply Structure.Embedding.ext
    intro x
    rfl
  have hmono := hf (EAB.symm e₁) (EAB.symm e₂)
  change χ (EA (uClosedComp U hU fR (EAB.symm e₁))) =
    χ (EA (uClosedComp U hU fR (EAB.symm e₂))) at hmono
  rw [hcomp e₁, hcomp e₂] at hmono
  exact hmono

/-- Exact bidirectional Ramsey-arrow correspondence for EVERY arbitrary
nonredundant reduced-language target, not just coherent canonical targets. -/
theorem uClosedArrowInto_iff_functional
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) X) (κ : Type*) :
    UClosedArrowInto A B U hU C κ ↔
      Structure.Arrow (A.asUFunctionsReduced U hU)
        (B.asUFunctionsReduced U hU) C κ := by
  constructor
  · exact functionalArrow_of_UClosedArrowInto A B U hU C κ
  · exact uClosedArrowInto_of_functional A B U hU C κ

end RelStructure
end StructuralRamsey
