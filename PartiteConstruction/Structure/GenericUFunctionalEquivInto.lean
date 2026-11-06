import PartiteConstruction.Structure.GenericUReducedLanguage

/-!
# U-closed source embeddings into arbitrary reduced functional targets

Do not duplicate U-relations in the target language. In particular, the
target below is an ARBITRARY set-valued-function structure: no coherence
condition is imposed, and every map operates on the original vertex carrier.
The two directions are inverse by embedding extensionality.

This module deliberately stops before the ordered Ramsey-arrow transfer.
-/

namespace StructuralRamsey

universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- A U-closed relational embedding into the decoder of an arbitrary mixed
functional target induces a full function embedding without re-encoding
or modifying the target. -/
def Embedding.toReducedUFunctionsTarget
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    {C : Structure (L.withUFunctionsReduced U) W}
    (e : Embedding A (Structure.toRelU U hU C))
    (he : IsUClosedEmbedding A (Structure.toRelU U hU C) U hU e) :
    Structure.Embedding (A.asUFunctionsReduced U hU) C where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    classical
    have hn : R.1 ∉ U := R.2
    simpa only [Structure.toRelU, dif_neg hn] using
      (e.map_rel_iff R.1 x)
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hr : (Structure.toRelU U hU C).rel F.1
          (e.toFun ∘ RelLanguage.appendU L U hU F x z) :=
        (e.map_rel_iff F.1
          (RelLanguage.appendU L U hU F x z)).mpr hz
      have hcomp := RelLanguage.appendU_comp L U hU F e.toFun x z
      have ht : (Structure.toRelU U hU C).rel F.1
          (RelLanguage.appendU L U hU F (e.toFun ∘ x) (e.toFun z)) :=
        Eq.mp (congrArg ((Structure.toRelU U hU C).rel F.1) hcomp) hr
      simpa only [Structure.toRelU, dif_pos F.2,
        RelLanguage.rootU_append, RelLanguage.lastU_append] using ht
    · intro hy
      have ht : (Structure.toRelU U hU C).rel F.1
          (RelLanguage.appendU L U hU F (e.toFun ∘ x) y) := by
        simpa only [Structure.toRelU, dif_pos F.2,
          RelLanguage.rootU_append, RelLanguage.lastU_append] using hy
      exact he F x y ht

/-- An arbitrary full functional embedding also yields the original
relational embedding of the source into the decoded target. -/
def Embedding.fromReducedUFunctionsTarget
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    {C : Structure (L.withUFunctionsReduced U) W}
    (f : Structure.Embedding (A.asUFunctionsReduced U hU) C) :
    Embedding A (Structure.toRelU U hU C) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    exact ((Structure.Embedding.toRelU U hU f).map_rel_iff R x).trans
      (toRelU_asUFunctionsReduced_rel_iff A U hU R x)

/-- Full functional embeddings have U-closed decoded range, and the
source's reduced-language round trip does not alter this property. -/
theorem Embedding.fromReducedUFunctionsTarget_uClosed
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    {C : Structure (L.withUFunctionsReduced U) W}
    (f : Structure.Embedding (A.asUFunctionsReduced U hU) C) :
    IsUClosedEmbedding A (Structure.toRelU U hU C) U hU
      (Embedding.fromReducedUFunctionsTarget U hU f) := by
  intro F x y hy
  obtain ⟨z, hz, hzy⟩ :=
    (Structure.Embedding.toRelU_uClosed U hU f) F x y hy
  exact ⟨z,
    (toRelU_asUFunctionsReduced_rel_iff A U hU F.1
      (RelLanguage.appendU L U hU F x z)).mp hz,
    hzy⟩

/-- Exact same-carrier equivalence, with an ARBITRARY target C. This is
stronger than the preliminary coherent/coherent source dictionary and
is the form needed for transporting arbitrary Ramsey colourings. -/
def uClosedEmbeddingEquivIntoTarget
    (A : RelStructure L V)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) W) :
    {e : Embedding A (Structure.toRelU U hU C) //
      IsUClosedEmbedding A (Structure.toRelU U hU C) U hU e} ≃
    Structure.Embedding (A.asUFunctionsReduced U hU) C where
  toFun e := e.1.toReducedUFunctionsTarget U hU e.2
  invFun f := ⟨Embedding.fromReducedUFunctionsTarget U hU f,
    Embedding.fromReducedUFunctionsTarget_uClosed U hU f⟩
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

end RelStructure
end StructuralRamsey
