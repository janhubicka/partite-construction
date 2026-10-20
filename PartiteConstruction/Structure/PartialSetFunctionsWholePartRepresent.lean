import PartiteConstruction.Structure.PartialSetFunctionsWholePartGraph

/-!
# Every transverse finite function value has a complete output-part tuple

A finite value set admits an enumeration of its outputs. Transversality says
the part map restricted to that set is injective, so the enumeration is
naturally indexed by pairwise distinct output parts, in a length bounded by
the number of parts. The lemma below supplies the missing source coverage
for the finite complete-value language.

No original input positions are assumed distinct, and empty defined values
are included. This is not yet an assertion about 2019 closure roots or
strict functional B-tree completions.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Every defined value of a finite transverse partial-function structure
has an enumeration respecting some finite injectively-labelled output
part tuple. The original full value, not a clipped fibre, is enumerated. -/
theorem completeOutputPartGraph_represents_value
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (U : Set V) (hValue : A.func F xs = some U) :
    ∃ (q : Language.CompleteOutputParts P)
      (ys : Fin q.size → V),
        Set.range ys = U ∧
        (∀ j : Fin q.size, part (ys j) = q.label j) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  let e : Fin (Fintype.card U) ≃ U :=
    (Fintype.equivFin U).symm
  let labels : Fin (Fintype.card U) → P :=
    fun j => part (e j).1
  let f : U → P := fun z => part z.1
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact hTrans F xs U hValue
      a.1 a.2 b.1 b.2 hab
  have hInjective : Function.Injective labels := by
    intro i j hij
    apply e.injective
    exact hf hij
  have hBound : Fintype.card U ≤ Fintype.card P :=
    Fintype.card_le_of_injective f hf
  let q : Language.CompleteOutputParts P :=
    ⟨⟨⟨Fintype.card U, Nat.lt_succ_of_le hBound⟩, labels⟩,
      hInjective⟩
  let ys : Fin q.size → V := fun i => (e i).1
  refine ⟨q, ys, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact (e j).2
    · intro hy
      let yu : U := ⟨y, hy⟩
      refine ⟨(Fintype.equivFin U) yu, ?_⟩
      change (e ((Fintype.equivFin U) yu)).1 = y
      exact congrArg Subtype.val
        ((Fintype.equivFin U).symm_apply_apply yu)
  · intro j
    rfl

end StructuralRamsey.PartialSetStructure
