import PartiteConstruction.Structure.GenericUOriginalOrderedArrow
import PartiteConstruction.Functional.OrderedRecursive

/-!
# Track F: the literal original arbitrary-relational (L,U) Ramsey theorem

This is the exact statement-generality gap behind survey thm:models2:
L is an arbitrary relational signature with one named order symbol; U is
an arbitrary set of other relation symbols of arity at least 2; A and B
are arbitrary finite correctly ordered L-structures. There are NO
irreducibility, local class completion, B-closedness, or U-transversality
hypotheses. The target is on the SAME finite witness carrier as the
positive-arity set-valued-function Ramsey theorem, and the named order
is restored from the witness's external LinearOrder.

The Ramsey arrow quantifies over actual induced relational embeddings
whose *ranges* are U-closed in the original signature.
-/

namespace StructuralRamsey

universe u v

namespace RelStructure

/-- Exact arbitrary (L,U) ordered Ramsey statement of the survey, with
every original quantifier and the literal original U-closed-range arrow.

It is stronger in colours: κ may be ANY finite nonempty colour type,
including Fin 2. No restriction on the relational signature cardinality
other than the finite natural arity attached to each symbol. -/
theorem originalOrderedUClosedRamsey
    (L : RelLanguage.{u}) (ord : L.Symbol)
    (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    {V W : Type v}
    (A : RelStructure L V) (B : RelStructure L W)
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (hA : A.NamedOrderCorrect ord hord)
    (hB : B.NamedOrderCorrect ord hord)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X)
      (C : RelStructure L X),
      (∀ t : Fin (L.arity ord) → X,
        C.rel ord t ↔
          @LT.lt X o.toLT
            (t (Fin.cast hord.symm (0 : Fin 2)))
            (t (Fin.cast hord.symm (1 : Fin 2)))) ∧
      OriginalUClosedArrow A B C U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR))
        κ := by
  let hU1 : ∀ R, R ∈ U → 1 ≤ L.arity R :=
    fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)
  let L0 := L.dropNamedOrder ord
  let U0 := L.dropNamedOrderU ord U
  let hU0 : ∀ R, R ∈ U0 → 1 ≤ L0.arity R :=
    fun R hR => hU1 R.1 hR
  have hU02 : ∀ R, R ∈ U0 → 2 ≤ L0.arity R :=
    fun R hR => hU R.1 hR
  have hpos : (L0.withUFunctionsReduced U0).PositiveFuncArity :=
    L0.withUFunctionsReduced_positive U0 hU02
  let A0 := A.dropNamedOrder ord
  let B0 := B.dropNamedOrder ord
  obtain ⟨X, hX, o, C, hArrow⟩ :=
    Structure.orderedRamsey
      (A0.asUFunctionsReduced U0 hU0)
      (B0.asUFunctionsReduced U0 hU0)
      hpos κ
  letI : LinearOrder X := o
  let D := Structure.toRelU U0 hU0 C
  let Crel := D.restoreNamedOrder hord
  refine ⟨X, hX, o, Crel, ?_, ?_⟩
  · intro t
    exact restoreNamedOrder_rel_order D hord t
  · exact originalUClosedArrow_of_functional
      ord hord U hordU hU1 A B hA hB C κ hArrow

end RelStructure
end StructuralRamsey
