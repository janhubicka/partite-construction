import PartiteConstruction.Functional.EHNConstruction
import PartiteConstruction.Functional.OrderedRecursive

/-! # EHN Ramsey theorem for relations and set-valued functions

The unrestricted ordered recursive theorem supplies the initial full Ramsey
witness. One class-preserving induced pass puts the reduct in the given
free-amalgamation class. Completing the order changes no function values.

Function symbols have positive input arity and genuinely set-valued outputs.
All embeddings in the conclusions are full (equivalently U-closed graph)
embeddings. The intermediate projection is only weak globally.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W X : Type v}

/-- Forget the distinguished order without changing any function fibre. -/
def Embedding.linearOrderReduct
    {A : Structure L.withLinearOrder U} {B : Structure L.withLinearOrder V}
    (e : Embedding A B) : Embedding A.linearOrderReduct B.linearOrderReduct where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff (.inl R) x
  map_func := e.map_func

theorem IsFreeAmalgam.linearOrderReduct
    {D : Structure L.withLinearOrder U} {A : Structure L.withLinearOrder V}
    {B : Structure L.withLinearOrder W} {C : Structure L.withLinearOrder X}
    {sA : Embedding D A} {sB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (h : IsFreeAmalgam sA sB iA iB) :
    IsFreeAmalgam sA.linearOrderReduct sB.linearOrderReduct
      iA.linearOrderReduct iB.linearOrderReduct where
  covers := h.covers
  overlap := h.overlap
  rel_iff R x := h.rel_iff (.inl R) x
  func_iff := h.func_iff

/-- Arbitrary interpretations of the extra order symbol over members of K.
Totality of the order is imposed only on A, B, and the completed witness. -/
def orderLiftClass (K : StructureClass (L := L)) :
    StructureClass (L := L.withLinearOrder) :=
  fun C => K C.linearOrderReduct

theorem FreeAmalgamationClass.orderLift
    {K : StructureClass (L := L)} (hK : FreeAmalgamationClass K) :
    FreeAmalgamationClass (orderLiftClass K) := by
  constructor
  · intro Y Z A B hB e
    exact hK.hereditary hB e.linearOrderReduct
  · intro H E F C D A B Cstr sA sB iA iB hA hB hfree
    exact hK.free hA hB hfree.linearOrderReduct

namespace FreeAmalgamationClass

/-- Ordered EHN for hereditary free-amalgamation classes with positive-arity
set-valued functions. The class need not contain the initial Ramsey witness. -/
theorem orderedRamsey
    {K : StructureClass (L := L)} (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : K A) (hB : K B) (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : Structure L W),
      K C ∧ Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  classical
  obtain ⟨P, hP, oP, C₀, hRamsey⟩ := Structure.orderedRamsey A B hpos κ
  letI : Finite P := hP
  letI : LinearOrder P := oP
  obtain ⟨T, hT⟩ := FunctionalPartite.EHN.inducedConstruction hK.orderLift
    A.withLinearOrder B.withLinearOrder C₀.withLinearOrder
    hA hB hpos.withLinearOrder κ hRamsey
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
  exact ⟨T.Carrier, T.finiteCarrier, o, T.system.toStructure.linearOrderReduct,
    T.mem, arrow_completeLinearOrder A B T.system.toStructure ho κ hT⟩

/-- The fixed-target form also holds: if A has no ordered copy in B, take B
itself; otherwise heredity supplies A's membership from that copy. -/
theorem orderedRamsey_of_mem_target
    {K : StructureClass (L := L)} (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hB : K B) (hpos : L.PositiveFuncArity)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : Structure L W),
      K C ∧ Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  classical
  by_cases h : Nonempty (Embedding A.withLinearOrder B.withLinearOrder)
  · obtain ⟨e⟩ := h
    exact hK.orderedRamsey A B (hK.hereditary hB e.linearOrderReduct) hB hpos κ
  · refine ⟨V, inferInstance, inferInstance, B, hB, ?_⟩
    intro χ
    refine ⟨Embedding.id B.withLinearOrder, ?_⟩
    intro e₁ e₂
    exact (h ⟨e₁⟩).elim

end FreeAmalgamationClass

/-- No member of the forbidden family has a full embedding into A. -/
def AvoidsEmbeddings (F : StructureClass (L := L)) : StructureClass (L := L) :=
  fun A => ∀ {Y : Type v} (E : Structure L Y), F E → Embedding E A → False

/-- Forbidding full irreducible structures gives a hereditary free-amalgamation
class also in the presence of set-valued functions. -/
theorem avoidsEmbeddings_freeAmalgamationClass
    (F : StructureClass (L := L))
    (hF : ∀ {Y : Type v} (E : Structure L Y), F E → E.Irreducible) :
    FreeAmalgamationClass (AvoidsEmbeddings F) := by
  constructor
  · intro Y Z A B hB e E J hJ j
    exact hB J hJ (e.comp j)
  · intro H E G C D A B Cstr sA sB iA iB hA hB hfree Y J hJ e
    rcases hF J hJ hfree e with hleft | hright
    · exact hA J hJ (e.factorThroughClosedRange iA hleft)
    · exact hB J hJ (e.factorThroughClosedRange iB hright)

/-- The survey's forbidden-irreducible functional Ramsey theorem, obtained as
a direct specialization of the class theorem rather than a separate proof. -/
theorem orderedRamsey_avoiding
    (F : StructureClass (L := L))
    (hF : ∀ {Y : Type v} (E : Structure L Y), F E → E.Irreducible)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : AvoidsEmbeddings F A) (hB : AvoidsEmbeddings F B)
    (hpos : L.PositiveFuncArity) (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : Structure L W),
      AvoidsEmbeddings F C ∧ Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ :=
  (avoidsEmbeddings_freeAmalgamationClass F hF).orderedRamsey A B hA hB hpos κ

end StructuralRamsey.Structure
