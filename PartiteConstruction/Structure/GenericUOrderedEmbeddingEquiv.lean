import PartiteConstruction.Structure.GenericUOrderedRestoration
import PartiteConstruction.Relational.Order

/-!
# Ordered-embedding form of the named-order reduct correspondence

The original survey names the binary order relation inside L. The checked
structural Ramsey theorem uses a fresh, external named order on the language
of its sources/targets. These two presentations have identical embeddings
when the old named order is correctly interpreted and the arbitrary witness
restores it from the external LinearOrder.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure.Embedding

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- A reduced relation embedding plus strict monotonicity is precisely a
full embedding between canonical fresh-order expansions. -/
def withOrderOfStrictMono
    {A : RelStructure L V} {B : RelStructure L W}
    [LinearOrder V] [LinearOrder W]
    (f : Embedding A B) (hf : StrictMono f) :
    Embedding A.ordered B.ordered where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact f.map_rel_iff R x
    | inr _ => exact hf.lt_iff_lt

/-- Forget only the fresh order relation. -/
def forgetFreshOrder
    {A : RelStructure L V} {B : RelStructure L W}
    [LinearOrder V] [LinearOrder W]
    (f : Embedding A.ordered B.ordered) :
    Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff R x := f.map_rel_iff (.inl R) x

/-- Ordered expansions and strictly monotone reduced maps have exactly
the same embedding type, on the same underlying vertex maps. -/
def equivFreshOrder
    (A : RelStructure L V) (B : RelStructure L W)
    [LinearOrder V] [LinearOrder W] :
    Embedding A.ordered B.ordered ≃
      {f : Embedding A B // StrictMono f} where
  toFun f := ⟨f.forgetFreshOrder, f.strictMono⟩
  invFun f := withOrderOfStrictMono f.1 f.2
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

/-- The exact arbitrary-target named-order embedding equivalence for
the original language L and its order-free reduct. All other relations,
including nullary symbols and repeated-coordinate tuples, are retained. -/
def equivNamedOrderFresh
    {ord : L.Symbol}
    (A : RelStructure L V)
    (D : RelStructure (L.dropNamedOrder ord) W)
    (hord : L.arity ord = 2)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord) :
    Embedding A (D.restoreNamedOrder hord) ≃
      Embedding (A.dropNamedOrder ord).ordered D.ordered where
  toFun e := withOrderOfStrictMono (e.toDroppedRestored hord)
    (strictMono_of_restored hord hA e)
  invFun f := ofDroppedRestored hord hA f.forgetFreshOrder f.strictMono
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Embedding.ext
    intro x
    rfl

end RelStructure.Embedding
end StructuralRamsey
