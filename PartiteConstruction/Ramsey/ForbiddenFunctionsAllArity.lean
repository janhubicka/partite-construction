import PartiteConstruction.Ramsey.ForbiddenFunctions
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

set_option autoImplicit false

/-! # Exact forbidden-pattern Ramsey theorem for arbitrary function arities

The unrestricted witness is supplied by the fixed-root all-arity theorem.
The class-preserving EHN pass itself now also allows constants, since its
initial copies are amalgamated over their canonical nullary root.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- The class of all structures is a hereditary free-amalgamation class. -/
def allStructures : StructureClass.{u,v} (L := L) := fun _ => True

theorem allStructures_free :
    FreeAmalgamationClass (allStructures (L := L)) := by
  refine {
    hereditary := ?_
    free := ?_
  }
  · intro Y Z A B hB e
    trivial
  · intro H E G C D A B Cstr sA sB iA iB hA hB hfree
    trivial

/-- Exact all-arity version of the survey's thm:HN. Forbidden patterns may
specify their order, their reducts need only be irreducible, and nullary
set-valued functions/constants are allowed. -/
theorem orderedRamsey_forbidden_expansions_allArity
    (F : StructureClass.{u,v} (L := L.withLinearOrder))
    (hF : ∀ {Y : Type v} (E : Structure L.withLinearOrder Y),
      F E → E.linearOrderReduct.Irreducible)
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : AvoidsEmbeddings F A.withLinearOrder)
    (hB : AvoidsEmbeddings F B.withLinearOrder)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : Structure L W),
      AvoidsEmbeddings F (@Structure.withLinearOrder L W C o.toLT) ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  classical
  have hAll :
      FreeAmalgamationClass (allStructures (L := L)) :=
    allStructures_free (L := L)
  obtain ⟨P, hP, oP, C₀, _, hRamsey⟩ :=
    StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
      hAll A B (by trivial) (by trivial) κ
  letI : Finite P := hP
  letI : LinearOrder P := oP
  obtain ⟨T, hT⟩ := FunctionalPartite.EHN.inducedConstruction_allArity
    (orderedForbiddenClass_free F hF)
    A.withLinearOrder B.withLinearOrder C₀.withLinearOrder
    ⟨hA, withLinearOrder_orderTotal A⟩
    ⟨hB, withLinearOrder_orderTotal B⟩
    κ hRamsey
  have hpart : ∀ x y, T.system.rel (.inr ()) ![x, y] →
      T.system.part x < T.system.part y := by
    intro x y hxy
    have h := T.isPartite.1.1 (.inr ()) ![x, y] hxy
    have ht :
        T.system.part ∘ ![x, y] =
          ![T.system.part x, T.system.part y] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp
      (congrArg (C₀.withLinearOrder.rel (.inr ())) ht) h
  obtain ⟨o, ho⟩ :=
    exists_linearOrder_extension T.system.toStructure T.system.part hpart
  letI : LinearOrder T.Carrier := o
  refine
    ⟨T.Carrier, T.finiteCarrier, o,
      T.system.toStructure.linearOrderReduct, ?_, ?_⟩
  · intro Y E hE e
    exact T.mem.1 E hE
      (e.beforeOrderCompletion (hF E hE) T.mem.2 ho)
  · exact arrow_completeLinearOrder A B T.system.toStructure ho κ hT

end StructuralRamsey.Structure
