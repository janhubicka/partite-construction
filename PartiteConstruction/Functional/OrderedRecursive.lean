import PartiteConstruction.Structure.Order
import PartiteConstruction.Functional.SemiClosedRecursiveConstruction
import PartiteConstruction.Functional.SingletonReduction
import PartiteConstruction.Ramsey.Ordered

/-! # The ordered recursive partite theorem

The local semi-closed construction and the closed repair are assembled with
ordinary finite ordered relational Ramsey, order completion, and the canonical
rank expansion.  The final theorem has no local-picture or Ramsey-witness
hypothesis.  Functions may be set-valued; their input arities are positive.
-/
namespace StructuralRamsey

universe u v
variable {L : Language.{u}} {U V P : Type v}

namespace RelStructure

/-- Replace the named order in the domain-expanded graph language by the
actual order of the carrier.  All other relations are left unchanged. -/
def completeNamedOrder
    (D : RelStructure L.withLinearOrder.withFunctionDomains.graph P)
    [LT P] : RelStructure L.withLinearOrder.withFunctionDomains.graph P where
  rel
    | .inl (.inl (.inl R)), x => D.rel (.inl (.inl (.inl R))) x
    | .inl (.inl (.inr _)), x => x 0 < x 1
    | .inl (.inr F), x => D.rel (.inl (.inr F)) x
    | .inr F, x => D.rel (.inr F) x

namespace Embedding

/-- An embedding of the canonical named-order graph is strictly monotone. -/
theorem namedOrder_strictMono
    {A : Structure L U} {B : Structure L V}
    [LinearOrder U] [LinearOrder V]
    (e : Embedding A.withLinearOrder.withFunctionDomains.graph
      B.withLinearOrder.withFunctionDomains.graph) : StrictMono e := by
  intro x y hxy
  exact (e.map_rel_iff (.inl (.inl (.inr ()))) ![x, y]).mpr hxy

/-- Add a duplicate order to the canonical encoded sources. -/
def duplicateNamedOrder
    {A : Structure L U} {B : Structure L V}
    [LinearOrder U] [LinearOrder V]
    (e : Embedding A.withLinearOrder.withFunctionDomains.graph
      B.withLinearOrder.withFunctionDomains.graph) :
    Embedding A.withLinearOrder.withFunctionDomains.graph.ordered
      B.withLinearOrder.withFunctionDomains.graph.ordered where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact e.map_rel_iff R x
    | inr _ => exact e.namedOrder_strictMono.lt_iff_lt

/-- The external order of an ordinary ordered Ramsey witness can replace the
internal named order when mapping the canonical sources into that witness. -/
def toNamedOrder
    {A : Structure L U} [LinearOrder U]
    {D : RelStructure L.withLinearOrder.withFunctionDomains.graph P}
    [LinearOrder P]
    (e : Embedding A.withLinearOrder.withFunctionDomains.graph.ordered
      D.ordered) :
    Embedding A.withLinearOrder.withFunctionDomains.graph
      D.completeNamedOrder where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    cases R with
    | inr F => exact e.map_rel_iff (.inl (.inr F)) x
    | inl R =>
      cases R with
      | inr F => exact e.map_rel_iff (.inl (.inl (.inr F))) x
      | inl R =>
        cases R with
        | inl R => exact e.map_rel_iff (.inl (.inl (.inl (.inl R)))) x
        | inr _ => exact e.strictMono.lt_iff_lt

end Embedding

/-- Ordinary ordered relational Ramsey supplies a finite witness whose named
order is exactly its carrier order.  No condition on function outputs is
assumed here; root pruning and the recursive construction impose it later. -/
theorem ordinaryWitness_namedOrder
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (P : Type v) (_ : Finite P) (o : LinearOrder P)
      (D : RelStructure L.withLinearOrder.withFunctionDomains.graph P),
      (∀ x : Fin 2 → P,
        D.rel (.inl (.inl (.inr ()))) x ↔
          @LT.lt P o.toLT (x 0) (x 1)) ∧
      StructuralRamsey.Arrow
        A.withLinearOrder.withFunctionDomains.graph
        B.withLinearOrder.withFunctionDomains.graph D κ := by
  obtain ⟨P, hP, o, E, hE⟩ :=
    Partite.orderedRamsey
      A.withLinearOrder.withFunctionDomains.graph
      B.withLinearOrder.withFunctionDomains.graph κ
  letI : LinearOrder P := o
  refine ⟨P, hP, o, E.completeNamedOrder, ?_, ?_⟩
  · intro x
    rfl
  · intro χ
    obtain ⟨f, hf⟩ := hE (fun e => χ e.toNamedOrder)
    refine ⟨f.toNamedOrder, ?_⟩
    intro e₁ e₂
    exact hf e₁.duplicateNamedOrder e₂.duplicateNamedOrder

end RelStructure

namespace Structure

/-- The unconditional ordered recursive theorem for singleton-valued partial
functions.  The output also has singleton-valued functions. -/
theorem orderedRamsey_singleton
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hpos : L.PositiveFuncArity)
    (hA : A.SingletonValued) (hB : B.SingletonValued)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : Structure L X),
      C.SingletonValued ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L X C o.toLT) κ := by
  obtain ⟨P, hP, oP, D, hDorder, hD⟩ :=
    RelStructure.ordinaryWitness_namedOrder A B κ
  letI : Finite P := hP
  letI : LinearOrder P := oP
  obtain ⟨X, hX, S, hSpart, hSsingle, _hSTrans, hSarrow⟩ :=
    Partite.SemiClosed.Recursive.recursiveConstruction_from_ordinaryWitness
      A.withLinearOrder B.withLinearOrder D
      hpos.withLinearOrder hA hB κ hD
  letI : Finite X := hX
  let T : Structure L.withLinearOrder X :=
    (Structure.ofGraph S.toRelStructure).functionDomainReduct
  have hTarrow : Arrow A.withLinearOrder B.withLinearOrder T κ :=
    arrow_forgetFunctionDomains A.withLinearOrder B.withLinearOrder
      (Structure.ofGraph S.toRelStructure) κ
      ((arrow_ofGraph_iff_closed S.toRelStructure κ).mpr hSarrow)
  have hpart :
      ∀ x y, T.rel (.inr ()) ![x, y] → S.part x < S.part y := by
    intro x y hxy
    have hp := hSpart.1 (.inl (.inl (.inr ()))) ![x, y] hxy
    change D.rel (.inl (.inl (.inr ()))) (S.part ∘ ![x, y]) at hp
    exact (hDorder (S.part ∘ ![x, y])).mp hp
  obtain ⟨oX, hExt⟩ := exists_linearOrder_extension T S.part hpart
  letI : LinearOrder X := oX
  refine ⟨X, hX, oX, T.linearOrderReduct, ?_, ?_⟩
  · intro F x y z hy hz
    exact hSsingle F x y z hy hz
  · exact arrow_completeLinearOrder A B T hExt κ hTarrow

/-- The unrestricted ordered structural Ramsey theorem for positive-arity
set-valued functions, obtained by the recursive partite construction.

The canonical rank expansion uses N=max(|A|,|B|); the singleton-valued theorem
constructs the witness, and forgetting the rank functions gives the full
original set-valued fibres.  The distinguished order is completed only in the
witness, and every embedding in the conclusion is a full function embedding.
-/
theorem orderedRamsey
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : Structure L X),
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L X C o.toLT) κ := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  let N := max (Fintype.card U) (Fintype.card V)
  have hposRank : (L.rankFunctions N).PositiveFuncArity := by
    intro F
    exact hpos F.1
  obtain ⟨X, hX, oX, C, _hCsingle, hC⟩ :=
    orderedRamsey_singleton (rankExpand A N) (rankExpand B N)
      hposRank (rankExpand_singletonValued A N)
      (rankExpand_singletonValued B N) κ
  letI : LinearOrder X := oX
  refine ⟨X, hX, oX, rankReduct C, ?_⟩
  exact arrow_of_singletonExpansion
    A.withLinearOrder B.withLinearOrder
    (fun e => e.strictMono) C.withLinearOrder κ hC

/-- Closed-graph formulation of the ordered recursive theorem.  This is the
relational U-closed arrow corresponding to full function embeddings. -/
theorem orderedClosedGraphRamsey
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : Structure L X),
      RelStructure.ClosedArrow
        A.withLinearOrder.graph B.withLinearOrder.graph
        (@Structure.withLinearOrder L X C o.toLT).graph κ := by
  obtain ⟨X, hX, o, C, hC⟩ := orderedRamsey A B hpos κ
  letI : LinearOrder X := o
  exact ⟨X, hX, o, C,
    (arrow_iff_closedGraph C.withLinearOrder κ).mp hC⟩

end Structure
end StructuralRamsey
