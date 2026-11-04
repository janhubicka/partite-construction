import PartiteConstruction.Functional.OrderedRecursive

/-!
# Generic U-closed relational signatures as set-valued-function languages

This is the same-carrier dictionary needed for the printed arbitrary-relational
\(L,U\) theorem in Appendix A of the survey. We deliberately RETAIN all original
relation symbols and add one redundant set-valued function for each designated
relation. This avoids a fragile deletion/reindexing of unrelated symbols.

For a designated m-ary relation R, the function has input arity m-1 and
F_R(x₀,...,x_{m-2}) = { y | R(x₀,...,x_{m-2},y) }.
Full preservation of F_R is equivalent to an induced relational embedding
with U-closed range, on precisely the same carriers and map.

The arbitrary-relational ordered Ramsey wrapper is a separate next step.
-/

namespace StructuralRamsey

universe u v w

namespace RelLanguage

/-- Retain every relation, adding a redundant set-valued function for each
distinguished closure relation. -/
def withUFunctions (L : RelLanguage.{u}) (U : Set L.Symbol) :
    Language.{u} where
  RelSymbol := L.Symbol
  FuncSymbol := U
  relArity := L.arity
  funcArity := fun F => L.arity F.1 - 1

/-- Distinguished arity at least two gives *positive* function input arity. -/
theorem withUFunctions_positive (L : RelLanguage.{u})
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R) :
    (L.withUFunctions U).PositiveFuncArity := by
  intro F
  change 0 < L.arity F.1 - 1
  have h := hU F.1 F.2
  omega

/-- Reconstruct the original tuple from its root and last value. The cast
identifies \`(m-1)+1\` with \`m\`; no vertex or output is introduced. -/
def appendU (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v}
    (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    Fin (L.arity F.1) → V :=
  fun i => Structure.funcTuple x y
    (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)).symm i)

@[simp] theorem appendU_comp
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v} {W : Type w}
    (f : V → W) (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    f ∘ appendU L U hU F x y =
      appendU L U hU F (f ∘ x) (f y) := by
  funext i
  change f (Structure.funcTuple x y
    (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)).symm i)) =
    Structure.funcTuple (f ∘ x) (f y)
      (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)).symm i)
  exact congrFun (Structure.comp_funcTuple f x y) _

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Same-carrier expansion of every designated relation to a multivalued
function. The original relations, including the distinguished ones, remain
available verbatim in the relational reduct. -/
def asUFunctions (A : RelStructure L V) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    Structure (L.withUFunctions U) V where
  rel R x := A.rel R x
  func F x := {y | A.rel F.1 (RelLanguage.appendU L U hU F x y)}

/-- The exact same-map requirement: every target output over an image root
comes from a source output. Relative to an induced relational embedding this
is precisely U-closedness, not total-fibre surjectivity imposed on a merely
relational homomorphism. -/
def IsUClosedEmbedding
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B) : Prop :=
  ∀ (F : U) (x : Fin (L.arity F.1 - 1) → V) (y : W),
    B.rel F.1 (RelLanguage.appendU L U hU F (e ∘ x) y) →
      ∃ z, A.rel F.1 (RelLanguage.appendU L U hU F x z) ∧ e z = y

/-- An induced relational embedding with the exact U-closure condition
becomes a FULL set-valued-function embedding on the identical map. -/
def Embedding.toUFunctions
    {A : RelStructure L V} {B : RelStructure L W}
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B) (he : IsUClosedEmbedding A B U hU e) :
    Structure.Embedding (A.asUFunctions U hU) (B.asUFunctions U hU) where
  toFun := e
  injective := e.injective
  map_rel_iff R x := e.map_rel_iff R x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hh : B.rel F.1
          (e ∘ RelLanguage.appendU L U hU F x z) :=
        (e.map_rel_iff F.1 (RelLanguage.appendU L U hU F x z)).mpr hz
      simpa only [RelLanguage.appendU_comp] using hh
    · intro hy
      exact he F x y hy

/-- Conversely a full functional embedding is already an induced relational
embedding, because all original relations were retained in the language. -/
def Embedding.fromUFunctions
    {A : RelStructure L V} {B : RelStructure L W}
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (f : Structure.Embedding (A.asUFunctions U hU) (B.asUFunctions U hU)) :
    Embedding A B where
  toFun := f
  injective := f.injective
  map_rel_iff R x := f.map_rel_iff R x

theorem Embedding.fromUFunctions_uClosed
    {A : RelStructure L V} {B : RelStructure L W}
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (f : Structure.Embedding (A.asUFunctions U hU) (B.asUFunctions U hU)) :
    IsUClosedEmbedding A B U hU (Embedding.fromUFunctions U hU f) := by
  intro F x y hy
  have hy' : y ∈ (B.asUFunctions U hU).func F (f ∘ x) := hy
  rw [← f.map_func F x] at hy'
  rcases hy' with ⟨z, hz, heq⟩
  exact ⟨z, hz, heq⟩

/-- The correspondence is exactly an equivalence of embedding TYPES:
in particular it does not enlarge the carriers or take function closure. -/
def uClosedEmbeddingEquiv
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol) (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    {e : Embedding A B // IsUClosedEmbedding A B U hU e} ≃
      Structure.Embedding (A.asUFunctions U hU) (B.asUFunctions U hU) where
  toFun e := e.1.toUFunctions U hU e.2
  invFun f := ⟨Embedding.fromUFunctions U hU f,
    Embedding.fromUFunctions_uClosed U hU f⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Structure.Embedding.ext
    intro x
    rfl

end RelStructure
end StructuralRamsey
