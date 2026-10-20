import PartiteConstruction.Functional.PartialFunctionPatternGraph2019

/-!
# Finiteness of relational structures and function-input patterns

For a finite relational signature and finite vertex carrier, only finitely
many relation interpretations exist. Likewise, a function-input equality
pattern has at most as many distinct root vertices as argument positions:
its argument map is surjective. These facts make the canonical whole-value
tag language finite once the original signature and the set of parts are
finite. No positivity assumption is needed for these finiteness facts.

This module does not assert that arbitrary tagged structures decode to
valid functions, or provide any functional target completion.
-/

namespace StructuralRamsey

universe u v

namespace RelStructure

variable {R : RelLanguage.{u}} {V : Type v}

/-- A relational structure is determined by its relation predicates. -/
theorem rel_injective :
    Function.Injective (fun A : RelStructure R V => A.rel) := by
  intro A B h
  cases A
  cases B
  cases h
  rfl

/-- A finite signature has only finitely many structures on a fixed
finite carrier. The arities may vary with the symbol. -/
instance [Finite R.Symbol] [Finite V] : Finite (RelStructure R V) := by
  classical
  exact Finite.of_injective (fun A : RelStructure R V => A.rel)
    rel_injective

end RelStructure

namespace Language.FunctionInputPattern

variable {L : Language.{u}}

/-- Every root label occurs as an argument, so the distinct-input root
has at most as many vertices as the original function has arguments. -/
theorem rootSize_le_arity (p : FunctionInputPattern L) :
    p.rootSize ≤ L.funcArity p.symbol := by
  have h := Fintype.card_le_of_surjective p.argMap p.onto
  simpa only [Fintype.card_fin] using h

/-- A bounded presentation of exactly the same equality-pattern data.
The zero-arity case has only the root of size zero. -/
def Bounded (L : Language.{u}) :=
  Σ (F : L.FuncSymbol), Σ (m : Fin (L.funcArity F + 1)),
    {r : Fin (L.funcArity F) → Fin m.val // Function.Surjective r}

/-- Record the proved root-size bound without changing the pattern. -/
def toBounded (p : FunctionInputPattern L) : Bounded L :=
  ⟨p.symbol, ⟨p.rootSize, Nat.lt_succ_of_le p.rootSize_le_arity⟩,
    ⟨p.argMap, p.onto⟩⟩

/-- Forget only the redundant bound in the bounded presentation. -/
def ofBounded (p : Bounded L) : FunctionInputPattern L where
  symbol := p.1
  rootSize := p.2.1.val
  argMap := p.2.2.val
  onto := p.2.2.property

@[simp] theorem ofBounded_toBounded (p : FunctionInputPattern L) :
    ofBounded (toBounded p) = p := by
  cases p
  rfl

/-- The bounded presentation loses no function-input pattern data. -/
theorem toBounded_injective :
    Function.Injective (toBounded : FunctionInputPattern L → Bounded L) :=
  Function.LeftInverse.injective ofBounded_toBounded

instance [Finite L.FuncSymbol] : Finite (Bounded L) := by
  unfold Bounded
  infer_instance

/-- Finitely many function symbols give finitely many equality patterns,
even though the original syntax allowed an arbitrary natural root size. -/
instance [Finite L.FuncSymbol] : Finite (FunctionInputPattern L) :=
  Finite.of_injective toBounded toBounded_injective

end Language.FunctionInputPattern

end StructuralRamsey
