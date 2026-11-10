import PartiteConstruction.Structure.GenericUFunctionalArrowEquivalence
import PartiteConstruction.Relational.Order
import PartiteConstruction.Structure.Order

/-!
# Ordered nonredundant functional / U-closed relational embedding dictionary

The generic U-functions replace, rather than duplicate, the distinguished
relations. The external strict order is represented by the ordinary
withLinearOrder expansion, not by a second independent order symbol.

The target here is an ARBITRARY reduced functional witness with an external
LinearOrder. All carriers, map composition, and complete function fibres are
unchanged. This module is independent of the old *named* order; the already
verified order-reduct bridge restores that symbol in the final step.

Proof candidates: require exact-head Lean/axiom audit before promotion.
-/

namespace StructuralRamsey
universe u v w z

namespace Structure.Embedding

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Forget only the fresh external named order, preserving every other
relation and the ENTIRE set-valued function fibre on the same map. -/
def forgetExternalOrder
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W]
    (f : Embedding A.withLinearOrder B.withLinearOrder) :
    Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff R x := f.map_rel_iff (.inl R) x
  map_func := f.map_func

/-- Expand an ordinary full function embedding by its strict monotonicity.
No new relation/function fibre is introduced by this step. -/
def withExternalOrder
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W]
    (f : Embedding A B) (hm : StrictMono f) :
    Embedding A.withLinearOrder B.withLinearOrder where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact f.map_rel_iff R x
    | inr _ => exact hm.lt_iff_lt
  map_func := f.map_func

/-- Same map proof that the only extra condition of an ordered full
function embedding is preservation of the strict external order. -/
def equivExternalOrder
    (A : Structure L V) (B : Structure L W)
    [LinearOrder V] [LinearOrder W] :
    Embedding A.withLinearOrder B.withLinearOrder ≃
      {f : Embedding A B // StrictMono f} where
  toFun f := ⟨f.forgetExternalOrder, f.strictMono⟩
  invFun f := f.1.withExternalOrder f.2
  left_inv := by
    intro f
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl

end Structure.Embedding

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Identity-on-vertex-map equivalence of *ordered* U-closed relational
embeddings with full embeddings of the ordered nonredundant function encoding,
even when the functional target is arbitrary and not a canonical encoding. -/
def uClosedOrderedEmbeddingEquivIntoTarget
    (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C : Structure (L.withUFunctionsReduced U) W)
    [LinearOrder V] [LinearOrder W] :
    {e : Embedding A (Structure.toRelU U hU C) //
      IsUClosedEmbedding A (Structure.toRelU U hU C) U hU e ∧
      StrictMono e} ≃
    Structure.Embedding
      (A.asUFunctionsReduced U hU).withLinearOrder
      C.withLinearOrder where
  toFun e :=
    let base := (uClosedEmbeddingEquivIntoTarget A U hU C)
      ⟨e.1, e.2.1⟩
    base.withExternalOrder e.2.2
  invFun f :=
    let base := (uClosedEmbeddingEquivIntoTarget A U hU C).symm
      f.forgetExternalOrder
    ⟨base.1, base.2, f.strictMono⟩
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

/-- A U-closed induced embedding that is strictly increasing with respect
to the external orders. -/
def OrderedUClosedEmbedding
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    [LinearOrder V] [LinearOrder W] : Type _ :=
  {e : Embedding A B // IsUClosedEmbedding A B U hU e ∧ StrictMono e}

/-- Actual composition of two U-closed, strictly monotone embeddings. -/
def orderedUClosedComp
    {X : Type z}
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    {B : RelStructure L W}
    {D : RelStructure L X}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (f : OrderedUClosedEmbedding B D U hU)
    (e : OrderedUClosedEmbedding A B U hU) :
    OrderedUClosedEmbedding A D U hU :=
  ⟨f.1.comp e.1, ⟨IsUClosedEmbedding.comp U hU f.1 f.2.1 e.1 e.2.1,
    f.2.2.comp e.2.2⟩⟩

@[simp] theorem orderedUClosedComp_apply
    {X : Type z}
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    {B : RelStructure L W}
    {D : RelStructure L X}
    [LinearOrder V] [LinearOrder W] [LinearOrder X]
    (f : OrderedUClosedEmbedding B D U hU)
    (e : OrderedUClosedEmbedding A B U hU)
    (x : V) :
    (orderedUClosedComp U hU f e).1 x = f.1 (e.1 x) := rfl

end RelStructure
end StructuralRamsey
