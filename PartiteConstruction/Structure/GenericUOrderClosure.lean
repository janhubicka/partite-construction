import PartiteConstruction.Structure.GenericUOrderedReduct

/-!
# U-closure is unchanged when deleting a distinct named order symbol

This module gives a direct, original-language closure contract: closure is
under the LAST coordinate of every designated relation, even if a relation
has other arguments equal or an empty value fibre. No function-graph
dictionary is assumed, so it is independent of the draft generic encoding.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure
variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Literal original relational U-closure of a vertex set. All root
coordinates of an R-tuple lie in S implies that its final coordinate is in S.
The hypothesis arity(R) ≥ 1 merely makes the root/last split defined. -/
def IsUClosedSetOn
    (B : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : Set V) : Prop :=
  ∀ (R : L.Symbol) (hR : R ∈ U)
    (t : Fin (L.arity R) → V),
    B.rel R t →
    (∀ i : Fin (L.arity R - 1),
      t (Fin.cast (Nat.sub_add_cancel (hU R hR)) i.castSucc) ∈ S) →
    t (Fin.cast (Nat.sub_add_cancel (hU R hR))
      (Fin.last (L.arity R - 1))) ∈ S

/-- Exact closure equivalence on the SAME vertex set after the named order
is removed; no tuple is changed and no relation outside U is restricted. -/
theorem isUClosedSetOn_dropNamedOrder
    (ord : L.Symbol) (U : Set L.Symbol)
    (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (B : RelStructure L V) (S : Set V) :
    B.IsUClosedSetOn U hU S ↔
      (B.dropNamedOrder ord).IsUClosedSetOn
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) S := by
  constructor
  · intro h R hR t hrel hroots
    exact h R.1 hR t hrel hroots
  · intro h R hR t hrel hroots
    have hn : R ≠ ord := by
      intro he
      exact hordU (he ▸ hR)
    exact h ⟨R, hn⟩ hR t hrel hroots

/-- The range of an induced embedding is U-closed in the original language. -/
def IsUClosedEmbeddingRange
    {A : RelStructure L V} {B : RelStructure L W}
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B) : Prop :=
  B.IsUClosedSetOn U hU (Set.range e.toFun)

/-- The predicate of closure of an embedding's range survives deletion of
the named order, without changing the underlying injection. -/
theorem isUClosedEmbeddingRange_dropNamedOrder
    (ord : L.Symbol) (U : Set L.Symbol)
    (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    IsUClosedEmbeddingRange U hU e ↔
      IsUClosedEmbeddingRange (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR) (e.dropNamedOrder ord) := by
  exact isUClosedSetOn_dropNamedOrder ord U hordU hU B
    (Set.range e.toFun)

end RelStructure
end StructuralRamsey
