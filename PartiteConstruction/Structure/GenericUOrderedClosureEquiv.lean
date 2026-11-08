import PartiteConstruction.Structure.GenericUOrderClosure
import PartiteConstruction.Structure.GenericUOrderedEmbeddingEquiv

/-!
# Same-carrier U-closed ordered embeddings after named-order deletion

This is an original-relational theorem: it uses actual last-coordinate
U-closure of the image, NOT a comparison with an arbitrary function graph.
Consequently it may be independently certified before the pending generic
function-language dictionary, and later composed with that dictionary.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure
variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- An arbitrary order-free target D acquires exactly the original
last-coordinate U-closure predicate after restoring the named order from
the external LinearOrder; no independent order predicate is retained. -/
theorem isUClosedSetOn_restoreNamedOrder
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (D : RelStructure (L.dropNamedOrder ord) V)
    [LinearOrder V] (S : Set V) :
    (D.restoreNamedOrder hord).IsUClosedSetOn U hU S ↔
      D.IsUClosedSetOn (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) S := by
  constructor
  · intro h R hR t hrel hroots
    apply h R.1 hR t
    · exact (restoreNamedOrder_rel_ne D hord R.1 R.2 t).mpr hrel
    · exact hroots
  · intro h R hR t hrel hroots
    have hn : R ≠ ord := by
      intro he
      exact hordU (he ▸ hR)
    exact h ⟨R, hn⟩ hR t
      ((restoreNamedOrder_rel_ne D hord R hn t).mp hrel) hroots

/-- Closedness of the *same* induced embedding range is equivalent before
and after restoration of the named order. -/
theorem isUClosedEmbeddingRange_restored
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V}
    (D : RelStructure (L.dropNamedOrder ord) W)
    [LinearOrder W]
    (e : Embedding A (D.restoreNamedOrder hord)) :
    IsUClosedEmbeddingRange U hU e ↔
      D.IsUClosedSetOn (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) (Set.range e.toFun) :=
  isUClosedSetOn_restoreNamedOrder ord hord U hordU hU D
    (Set.range e.toFun)

/-- Exact embedding-type dictionary for the old named-order signature,
including the true U-closed range requirement. Every map stays literally
the same injection; the arbitrary reduced target needs no coherence
hypothesis and nullary ordinary relations are retained. -/
def uClosedEquivNamedOrderFresh
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (A : RelStructure L V)
    (D : RelStructure (L.dropNamedOrder ord) W)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord) :
    {e : Embedding A (D.restoreNamedOrder hord) //
      IsUClosedEmbeddingRange U hU e} ≃
    {f : Embedding (A.dropNamedOrder ord).ordered D.ordered //
      D.IsUClosedSetOn (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) (Set.range f.toFun)} where
  toFun e :=
    ⟨Embedding.equivNamedOrderFresh A D hord hA e.1,
      (isUClosedEmbeddingRange_restored ord hord U hordU hU D e.1).mp e.2⟩
  invFun f :=
    ⟨(Embedding.equivNamedOrderFresh A D hord hA).symm f.1,
      (isUClosedEmbeddingRange_restored ord hord U hordU hU D
        ((Embedding.equivNamedOrderFresh A D hord hA).symm f.1)).mpr f.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl

end RelStructure
end StructuralRamsey
