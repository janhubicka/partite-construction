import PartiteConstruction.Structure.GenericUOriginalOrderedEmbedding

/-!
# Track F: the literal original U-closed ordered Ramsey arrow

The only U-closedness convention used in the external theorem below is
closure of the RANGE of a genuine induced relational embedding. Both the
named order and non-U relations are interpreted in the original signature.

This module transports actual colouring/embedding composition to the
functional witness, on the same vertex maps. It is a proof candidate until
the exact-head Lean build and axiom audit pass; no manuscript is edited.
-/

namespace StructuralRamsey

universe u v w z

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w} {X : Type z}

/-- Genuine original-language embeddings with U-closed range compose.
Their composition is exactly the ordinary vertex-map composition. -/
def uClosedRangeComp
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    (f : {e : Embedding B C // IsUClosedEmbeddingRange U hU e})
    (e : {e : Embedding A B // IsUClosedEmbeddingRange U hU e}) :
    {g : Embedding A C // IsUClosedEmbeddingRange U hU g} :=
  ⟨f.1.comp e.1,
    (isUClosedEmbedding_iff_range U hU (f.1.comp e.1)).mp
      (IsUClosedEmbedding.comp U hU f.1
        ((isUClosedEmbedding_iff_range U hU f.1).mpr f.2)
        e.1 ((isUClosedEmbedding_iff_range U hU e.1).mpr e.2))⟩

@[simp] theorem uClosedRangeComp_apply
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    (f : {e : Embedding B C // IsUClosedEmbeddingRange U hU e})
    (e : {e : Embedding A B // IsUClosedEmbeddingRange U hU e})
    (x : V) :
    (uClosedRangeComp U hU f e).1 x = f.1 (e.1 x) := rfl

/-- The original (not function-graph) closed Ramsey arrow: colour all
induced embeddings with U-closed range and compose the actual maps. -/
def OriginalUClosedArrow
    (A : RelStructure L V) (B : RelStructure L W)
    (C : RelStructure L X)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) : Prop :=
  ∀ χ : {e : Embedding A C // IsUClosedEmbeddingRange U hU e} → κ,
    ∃ f : {e : Embedding B C // IsUClosedEmbeddingRange U hU e},
      ∀ e₁ e₂ : {e : Embedding A B // IsUClosedEmbeddingRange U hU e},
        χ (uClosedRangeComp U hU f e₁) =
          χ (uClosedRangeComp U hU f e₂)

namespace Embedding

/-- Every old-language embedding between correctly named-order structures
maps into the order-restored reduct by the IDENTICAL injection. -/
def toRestoredCorrectOrder
    (ord : L.Symbol) (hord : L.arity ord = 2)
    {A : RelStructure L V} {B : RelStructure L W}
    [LinearOrder W]
    (hB : B.NamedOrderCorrect ord hord)
    (e : Embedding A B) :
    Embedding A ((B.dropNamedOrder ord).restoreNamedOrder hord) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R t
    exact (restore_dropNamedOrder_rel_iff B ord hord hB R
      (e.toFun ∘ t)).trans (e.map_rel_iff R t)

/-- Every induced embedding between structures whose named order agrees
with their carrier linear orders is strictly monotone. -/
theorem strictMono_of_correctNamedOrder
    (ord : L.Symbol) (hord : L.arity ord = 2)
    {A : RelStructure L V} {B : RelStructure L W}
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord)
    (hB : B.NamedOrderCorrect ord hord)
    (e : Embedding A B) : StrictMono e :=
  strictMono_of_restored hord hA (e.toRestoredCorrectOrder ord hord hB)

end Embedding

/-- Send an original-L U-closed A-copy of B to the full ordered-function
embedding between their nonredundant encodings. All relation symbols except
the named order are preserved verbatim. -/
def originalUClosedEmbedding_toFunctional
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord)
    (hB : B.NamedOrderCorrect ord hord)
    (e : {g : Embedding A B // IsUClosedEmbeddingRange U hU g}) :
    Structure.Embedding
      ((A.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder
      ((B.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder := by
  let U0 := L.dropNamedOrderU ord U
  let hU0 : ∀ R, R ∈ U0 → 1 ≤ (L.dropNamedOrder ord).arity R :=
    fun R hR => hU R.1 hR
  let e0 := e.1.dropNamedOrder ord
  have hrange : IsUClosedEmbeddingRange U0 hU0 e0 :=
    (isUClosedEmbeddingRange_dropNamedOrder ord U hordU hU e.1).mp e.2
  have hlift : IsUClosedEmbedding (A.dropNamedOrder ord)
      (B.dropNamedOrder ord) U0 hU0 e0 :=
    (isUClosedEmbedding_iff_range U0 hU0 e0).mpr hrange
  have hmono : StrictMono e0 :=
    e.1.strictMono_of_correctNamedOrder ord hord hA hB
  exact (e0.toReducedUFunctions U0 hU0 hlift).withExternalOrder hmono

/-- Unconditional transfer of a genuine ordered functional Ramsey arrow
to the EXACT original-language named-order, U-closed-range arrow. -/
theorem originalUClosedArrow_of_functional
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (A : RelStructure L V) (B : RelStructure L W)
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (hA : A.NamedOrderCorrect ord hord)
    (hB : B.NamedOrderCorrect ord hord)
    (C : Structure ((L.dropNamedOrder ord).withUFunctionsReduced
      (L.dropNamedOrderU ord U)) X)
    (κ : Type*)
    (hRamsey : Structure.Arrow
      ((A.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder
      ((B.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder
      C.withLinearOrder κ) :
    OriginalUClosedArrow A B
      ((Structure.toRelU (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) C).restoreNamedOrder hord) U hU κ := by
  let EA := originalUClosedEmbeddingEquivIntoTarget
    ord hord U hordU hU A hA C
  let EB := originalUClosedEmbeddingEquivIntoTarget
    ord hord U hordU hU B hB C
  intro χ
  let χF : Structure.Embedding
      ((A.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder
      C.withLinearOrder → κ :=
    fun e => χ (EA.symm e)
  obtain ⟨f, hf⟩ := hRamsey χF
  refine ⟨EB.symm f, ?_⟩
  intro e₁ e₂
  let e₁F := originalUClosedEmbedding_toFunctional
    ord hord U hordU hU hA hB e₁
  let e₂F := originalUClosedEmbedding_toFunctional
    ord hord U hordU hU hA hB e₂
  have hc (e : {g : Embedding A B // IsUClosedEmbeddingRange U hU g}) :
      EA.symm (f.comp
        (originalUClosedEmbedding_toFunctional
          ord hord U hordU hU hA hB e)) =
      uClosedRangeComp U hU (EB.symm f) e := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  have hχ := hf e₁F e₂F
  change χ (EA.symm (f.comp e₁F)) =
    χ (EA.symm (f.comp e₂F)) at hχ
  change χ (uClosedRangeComp U hU (EB.symm f) e₁) =
    χ (uClosedRangeComp U hU (EB.symm f) e₂)
  rw [← hc e₁, ← hc e₂]
  exact hχ

end RelStructure
end StructuralRamsey
