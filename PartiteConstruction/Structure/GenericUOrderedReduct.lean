import PartiteConstruction.Relational.Basic

/-!
# Dropping the distinguished order from an arbitrary relational language

For Appendix A's generic (L,U) translation, the named order relation must
be removed before the ordered functional Ramsey witness is constructed.
Keeping both the named order and the external LinearOrder would allow an
incoherent target, so the final encoding cannot duplicate this symbol.

This module builds the order-free relational language and transports
*actual induced embeddings* on the same vertex maps.  It is an independent
foundational step: it does not assert the final ordered Ramsey theorem,
and it does not depend on the draft generic U-function dictionary.
-/

namespace StructuralRamsey

universe u v w z

namespace RelLanguage

/-- Retain exactly those original relational symbols distinct from the
distinguished named order; preserve arities, including arity zero. -/
def dropNamedOrder (L : RelLanguage.{u}) (ord : L.Symbol) :
    RelLanguage.{u} where
  Symbol := {R : L.Symbol // R ≠ ord}
  arity := fun R => L.arity R.1

/-- The designated closure symbols in the order-free relational language.
Only the named order is omitted, with no extra symbol duplication. -/
def dropNamedOrderU (L : RelLanguage.{u}) (ord : L.Symbol)
    (U : Set L.Symbol) : Set (L.dropNamedOrder ord).Symbol :=
  fun R => R.1 ∈ U

/-- Distinguished U-symbol arity is preserved exactly by order deletion.
The hypothesis ord ∉ U belongs to the final ordered theorem's contract,
not to this source-intrinsic arity lemma. -/
theorem dropNamedOrderU_arity_two
    (L : RelLanguage.{u}) (ord : L.Symbol) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    (R : (L.dropNamedOrder ord).Symbol)
    (hR : R ∈ L.dropNamedOrderU ord U) :
    2 ≤ (L.dropNamedOrder ord).arity R :=
  hU R.1 hR

/-- Deleting the named order loses NO designated closure symbols when
ord ∉ U.  This explicit equivalence will reindex the final function sort. -/
def dropNamedOrderUEquiv
    (L : RelLanguage.{u}) (ord : L.Symbol)
    (U : Set L.Symbol) (hordU : ord ∉ U) :
    U ≃ L.dropNamedOrderU ord U where
  toFun F := ⟨⟨F.1, fun h => hordU (h ▸ F.2)⟩, F.2⟩
  invFun F := ⟨F.1.1, F.2⟩
  left_inv := by
    intro F
    apply Subtype.ext
    rfl
  right_inv := by
    intro F
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The symbol equivalence changes neither relation nor function arity. -/
@[simp] theorem dropNamedOrderUEquiv_arity
    (L : RelLanguage.{u}) (ord : L.Symbol)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (F : U) :
    (L.dropNamedOrder ord).arity
      ((L.dropNamedOrderUEquiv ord U hordU F).1) = L.arity F.1 := rfl

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}
variable {X : Type z}

/-- Forget the named order as a relation symbol, without changing the
carrier or the interpretation of any other relation. -/
def dropNamedOrder (A : RelStructure L V) (ord : L.Symbol) :
    RelStructure (L.dropNamedOrder ord) V where
  rel R x := A.rel R.1 x

@[simp] theorem dropNamedOrder_rel_iff
    (A : RelStructure L V) (ord : L.Symbol)
    (R : (L.dropNamedOrder ord).Symbol)
    (x : Fin ((L.dropNamedOrder ord).arity R) → V) :
    (A.dropNamedOrder ord).rel R x ↔ A.rel R.1 x := Iff.rfl

/-- Source contract for the omitted named order: it must be precisely the
strict carrier order, not merely an acyclic or included relation. -/
def NamedOrderCorrect (A : RelStructure L V) (ord : L.Symbol)
    (hord : L.arity ord = 2) [LT V] : Prop :=
  ∀ t : Fin (L.arity ord) → V,
    A.rel ord t ↔
      t (Fin.cast hord.symm (0 : Fin 2)) <
      t (Fin.cast hord.symm (1 : Fin 2))

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W}
variable {C : RelStructure L X}

/-- The literal induced-embedding map survives deletion of the named order.
This does not claim that an arbitrary reduced embedding preserves order:
that is supplied separately by the external ordered expansion. -/
def dropNamedOrder (f : Embedding A B) (ord : L.Symbol) :
    Embedding (A.dropNamedOrder ord) (B.dropNamedOrder ord) where
  toFun := f
  injective := f.injective
  map_rel_iff R x := f.map_rel_iff R.1 x

@[simp] theorem dropNamedOrder_id (ord : L.Symbol) (A : RelStructure L V) :
    (Embedding.id A).dropNamedOrder ord =
      Embedding.id (A.dropNamedOrder ord) := by
  apply Embedding.ext
  intro x
  rfl

@[simp] theorem dropNamedOrder_comp (ord : L.Symbol)
    (f : Embedding B C) (g : Embedding A B) :
    (f.comp g).dropNamedOrder ord =
      (f.dropNamedOrder ord).comp (g.dropNamedOrder ord) := by
  apply Embedding.ext
  intro x
  rfl

end Embedding
end RelStructure
end StructuralRamsey
