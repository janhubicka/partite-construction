import PartiteConstruction.Functional.OrderedRecursive

/-!
# Generic U-closed relational signatures as set-valued-function languages

This is a PRELIMINARY same-carrier dictionary for Appendix A. It
deliberately RETAINS all original relations and adds a redundant function
for each distinguished U-relation. It is suitable for comparing full
embeddings BETWEEN CANONICALLY COHERENT SOURCES AND TARGETS.

For a designated m-ary R the extra function has input arity m-1, with
F_R(x₀,...,x_{m-2}) = { y | R(x₀,...,x_{m-2},y) }.
Full preservation of F_R is equivalent to U-closedness of an induced
relational embedding between these coherent expansions, on the same map.

CRITICAL: An arbitrary functional Ramsey witness need NOT remain coherent:
its duplicated R relation and F_R function graph may disagree. Thus this
dictionary ALONE cannot transfer an unrestricted functional Ramsey arrow.
The final theorem must use the NONREDUNDANT signature replacing U-relations
by functions, and separately handle the designated order.
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
    (Fin.cast ((Nat.sub_add_cancel (hU F.1 F.2)).symm) i)

@[simp] theorem appendU_comp
    (L : RelLanguage.{u}) (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) {V : Type v} {W : Type w}
    (f : V → W) (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    f ∘ appendU L U hU F x y =
      appendU L U hU F (f ∘ x) (f y) := by
  funext i
  change f (Structure.funcTuple x y
    (Fin.cast ((Nat.sub_add_cancel (hU F.1 F.2)).symm) i)) =
    Structure.funcTuple (f ∘ x) (f y)
      (Fin.cast ((Nat.sub_add_cancel (hU F.1 F.2)).symm) i)
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
      -- Rewrite with the explicit function-tuple naturality law.  A
      -- simplifier-only application does not elaborate the local coercion.
      have hcomp := RelLanguage.appendU_comp L U hU F e.toFun x z
      exact Eq.mp (congrArg (B.rel F.1) hcomp) hh
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
