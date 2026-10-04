import PartiteConstruction.Ramsey.FreeAmalgamationFunctions

/-! # Ordered forbidden structures with irreducible functional reducts

The survey forbids ordered structures, not necessarily every ordering of a
forbidden reduct. We therefore preserve the additional invariant that the
partial order is already total on each full irreducible reduct. Completing
the order cannot create a new forbidden embedding on such a reduct.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W X : Type v}

/-- Irreducibility of an order reduct implies irreducibility of its expansion. -/
theorem irreducible_of_linearOrderReduct
    (A : Structure L.withLinearOrder U) (hA : A.linearOrderReduct.Irreducible) :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  exact hA hfree.linearOrderReduct e.linearOrderReduct

theorem Embedding.orderPair_iff
    {A : Structure L.withLinearOrder U} {B : Structure L.withLinearOrder V}
    (e : Embedding A B) (x y : U) :
    B.rel (.inr ()) ![e x, e y] ↔ A.rel (.inr ()) ![x, y] := by
  have ht : e ∘ ![x, y] = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  rw [← ht]
  exact e.map_rel_iff (.inr ()) ![x, y]

/-- Every full irreducible reduct already has all its distinct pairs ordered. -/
def OrderTotalOnIrreducibles (C : Structure L.withLinearOrder W) : Prop :=
  ∀ {Y : Type v} (E : Structure L Y), E.Irreducible →
    ∀ e : Embedding E C.linearOrderReduct, ∀ x y : Y, x ≠ y →
      C.rel (.inr ()) ![e x, e y] ∨ C.rel (.inr ()) ![e y, e x]

theorem OrderTotalOnIrreducibles.hereditary
    {A : Structure L.withLinearOrder U} {B : Structure L.withLinearOrder V}
    (hB : B.OrderTotalOnIrreducibles) (j : Embedding A B) :
    A.OrderTotalOnIrreducibles := by
  intro Y E hE e x y hxy
  rcases hB E hE (j.linearOrderReduct.comp e) x y hxy with h | h
  · exact Or.inl ((j.orderPair_iff (e x) (e y)).mp h)
  · exact Or.inr ((j.orderPair_iff (e y) (e x)).mp h)

theorem OrderTotalOnIrreducibles.free
    {D : Structure L.withLinearOrder U} {A : Structure L.withLinearOrder V}
    {B : Structure L.withLinearOrder W} {C : Structure L.withLinearOrder X}
    {sA : Embedding D A} {sB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hA : A.OrderTotalOnIrreducibles) (hB : B.OrderTotalOnIrreducibles)
    (hfree : IsFreeAmalgam sA sB iA iB) : C.OrderTotalOnIrreducibles := by
  intro Y E hE e x y hxy
  rcases hE hfree.linearOrderReduct e with hleft | hright
  · choose q hq using hleft
    let f := e.factorWithMap iA.linearOrderReduct q hq
    have hqx (z : Y) : e z = iA (q z) := hq z
    rcases hA E hE f x y hxy with h | h
    · have hC := (iA.orderPair_iff (q x) (q y)).mpr h
      rw [← hqx x, ← hqx y] at hC
      exact Or.inl hC
    · have hC := (iA.orderPair_iff (q y) (q x)).mpr h
      rw [← hqx x, ← hqx y] at hC
      exact Or.inr hC
  · choose q hq using hright
    let f := e.factorWithMap iB.linearOrderReduct q hq
    have hqx (z : Y) : e z = iB (q z) := hq z
    rcases hB E hE f x y hxy with h | h
    · have hC := (iB.orderPair_iff (q x) (q y)).mpr h
      rw [← hqx x, ← hqx y] at hC
      exact Or.inl hC
    · have hC := (iB.orderPair_iff (q y) (q x)).mpr h
      rw [← hqx x, ← hqx y] at hC
      exact Or.inr hC

theorem withLinearOrder_orderTotal (A : Structure L U) [LinearOrder U] :
    A.withLinearOrder.OrderTotalOnIrreducibles := by
  intro Y E _ e x y hxy
  have hne : e x ≠ e y := fun h => hxy (e.injective h)
  exact lt_or_gt_of_ne hne

/-- Comparisons on an irreducible reduct are unchanged by any linear extension. -/
theorem OrderTotalOnIrreducibles.orderPair_complete_iff
    {C : Structure L.withLinearOrder W} [LinearOrder W]
    (hC : C.OrderTotalOnIrreducibles)
    (hExt : ∀ x y, C.rel (.inr ()) ![x, y] → x < y)
    {E : Structure L U} (hE : E.Irreducible)
    (e : Embedding E C.linearOrderReduct) (x y : U) :
    C.rel (.inr ()) ![e x, e y] ↔ e x < e y := by
  constructor
  · exact hExt (e x) (e y)
  · intro hlt
    have hxy : x ≠ y := by
      intro heq
      rw [heq] at hlt
      exact (lt_irrefl _ hlt)
    rcases hC E hE e x y hxy with h | h
    · exact h
    · exact (lt_asymm hlt (hExt (e y) (e x) h)).elim

/-- An embedding with irreducible reduct into a completed order was already
an embedding into the original partial-order structure. -/
def Embedding.beforeOrderCompletion
    {A : Structure L.withLinearOrder U} {C : Structure L.withLinearOrder W}
    [LinearOrder W] (hA : A.linearOrderReduct.Irreducible)
    (hC : C.OrderTotalOnIrreducibles)
    (hExt : ∀ x y, C.rel (.inr ()) ![x, y] → x < y)
    (e : Embedding A C.linearOrderReduct.withLinearOrder) : Embedding A C where
  toFun := e
  injective := e.injective
  map_func := e.map_func
  map_rel_iff := by
    intro R x
    cases R with
    | inl R => exact e.map_rel_iff (.inl R) x
    | inr r =>
      cases r
      have ht : e ∘ x = ![e (x (0 : Fin 2)), e (x (1 : Fin 2))] := by
        funext i
        fin_cases i <;> rfl
      change C.rel (.inr ()) (e ∘ x) ↔ A.rel (.inr ()) x
      rw [ht, hC.orderPair_complete_iff hExt hA e.linearOrderReduct]
      exact e.map_rel_iff (.inr ()) x

/-- The auxiliary class keeps both the forbidden ordered patterns and the
comparability needed when completing the order. -/
def orderedForbiddenClass (F : StructureClass (L := L.withLinearOrder)) :
    StructureClass (L := L.withLinearOrder) :=
  fun C => AvoidsEmbeddings F C ∧ C.OrderTotalOnIrreducibles

theorem orderedForbiddenClass_free
    (F : StructureClass (L := L.withLinearOrder))
    (hF : ∀ {Y : Type v} (E : Structure L.withLinearOrder Y),
      F E → E.linearOrderReduct.Irreducible) :
    FreeAmalgamationClass (orderedForbiddenClass F) := by
  have hAvoid := avoidsEmbeddings_freeAmalgamationClass F
    (fun E h => irreducible_of_linearOrderReduct E (hF E h))
  constructor
  · intro Y Z A B hB e
    exact ⟨hAvoid.hereditary hB.1 e, hB.2.hereditary e⟩
  · intro H E G C D A B Cstr sA sB iA iB hA hB hfree
    exact ⟨hAvoid.free hA.1 hB.1 hfree, hA.2.free hB.2 hfree⟩

/-- Exact positive-arity version of the survey's thm:HN. Forbidden patterns
may specify an order; only their function/relation reducts must be irreducible. -/
theorem orderedRamsey_forbidden_expansions
    (F : StructureClass (L := L.withLinearOrder))
    (hF : ∀ {Y : Type v} (E : Structure L.withLinearOrder Y),
      F E → E.linearOrderReduct.Irreducible)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : AvoidsEmbeddings F A.withLinearOrder)
    (hB : AvoidsEmbeddings F B.withLinearOrder)
    (hpos : L.PositiveFuncArity) (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : Structure L W),
      AvoidsEmbeddings F (@Structure.withLinearOrder L W C o.toLT) ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  classical
  obtain ⟨P, hP, oP, C₀, hRamsey⟩ := Structure.orderedRamsey A B hpos κ
  letI : Finite P := hP
  letI : LinearOrder P := oP
  obtain ⟨T, hT⟩ := FunctionalPartite.EHN.inducedConstruction
    (orderedForbiddenClass_free F hF)
    A.withLinearOrder B.withLinearOrder C₀.withLinearOrder
    ⟨hA, withLinearOrder_orderTotal A⟩ ⟨hB, withLinearOrder_orderTotal B⟩
    hpos.withLinearOrder κ hRamsey
  have hpart : ∀ x y, T.system.rel (.inr ()) ![x, y] →
      T.system.part x < T.system.part y := by
    intro x y hxy
    have h := T.over.1.1 (.inr ()) ![x, y] hxy
    have ht : T.system.part ∘ ![x, y] = ![T.system.part x, T.system.part y] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp (congrArg (C₀.withLinearOrder.rel (.inr ())) ht) h
  obtain ⟨o, ho⟩ := exists_linearOrder_extension T.system.toStructure T.system.part hpart
  letI : LinearOrder T.Carrier := o
  refine ⟨T.Carrier, T.finiteCarrier, o, T.system.toStructure.linearOrderReduct, ?_, ?_⟩
  · intro Y E hE e
    exact T.mem.1 E hE (e.beforeOrderCompletion (hF E hE) T.mem.2 ho)
  · exact arrow_completeLinearOrder A B T.system.toStructure ho κ hT

end StructuralRamsey.Structure
