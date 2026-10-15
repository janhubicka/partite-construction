import PartiteConstruction.Structure.Basic

/-!
# Partial set-valued functions: undefined is NOT the empty value

The survey's older total-fibre representation uses
  F : V^r → Set V
and encodes an undefined input by an empty fibre. This is perfectly
adequate for the restricted class of partial functions where every
DEFINED value set is nonempty, but it cannot represent a defined
operation whose value is genuinely empty.

The source-faithful general syntax is
  F : V^r → Option (Set V).
Here `none` means undefined, while `some ∅` means DEFINED with no
outputs. A partial homomorphism preserves all defined source inputs,
including those with empty values, but makes no assertion on inputs
which are undefined in the source. A full/domain-reflecting
homomorphism instead preserves the entire Option value.

This is a separate proof interface: the existing `Structure`,
`IsEHNHomomorphismEmbedding`, `OriginalPartialSemantics`, all
recursion and Ramsey theorems are left unchanged. The existing
original-partial <-> EHN equivalence holds only for the previously
encoded nonempty-defined-fibre convention, not automatically for
this richer semantics.

The weak restriction below deliberately drops a nonempty output
whose entire image is forgotten, while retaining an ORIGINAL
defined-empty input as defined-empty. It also retains the nonempty
surviving part of a genuinely set-valued output. This convention
needs to be kept separate from simply restricting the domain and
graph as ordinary relational induced substructures.
-/

namespace StructuralRamsey

universe u v w

/-- Independent definedness and set-valued output. -/
structure PartialSetStructure (L : Language.{u}) (V : Type v) where
  rel : (R : L.RelSymbol) → (Fin (L.relArity R) → V) → Prop
  func : (F : L.FuncSymbol) →
    (Fin (L.funcArity F) → V) → Option (Set V)

namespace PartialSetStructure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A defined input, EVEN IF its output set is empty. -/
def Defined (A : PartialSetStructure L V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) : Prop :=
  ∃ S : Set V, A.func F x = some S

/-- The output-incidence relation, independent of the domain
predicate. Defined-empty inputs have no incidences but DO belong to
the domain. -/
def HasOutput (A : PartialSetStructure L V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (y : V) : Prop :=
  ∃ S : Set V, A.func F x = some S ∧ y ∈ S

/-- 2019-style partial function homomorphism: defined source
inputs are mapped to defined target inputs with exactly the
image set as value. No condition is imposed on undefined
source inputs. In particular defined-empty must remain
DEFINED-empty, not become undefined. -/
def IsOriginalPartialHomomorphism
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) : Prop :=
  (∀ R x, A.rel R x → B.rel R (f ∘ x)) ∧
  (∀ F x S, A.func F x = some S →
    B.func F (f ∘ x) = some (Structure.imageSet f S))

/-- The stronger total-fibre convention, now with explicit
domain reflection (the entire Option must be equal). -/
def IsDomainReflectingHomomorphism
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) : Prop :=
  (∀ R x, A.rel R x → B.rel R (f ∘ x)) ∧
  (∀ F x, (A.func F x).map (Structure.imageSet f) =
    B.func F (f ∘ x))

/-- Full/domain-reflecting homomorphisms also preserve all
defined source inputs. The converse does NOT hold. -/
theorem IsDomainReflectingHomomorphism.toOriginalPartial
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (h : IsDomainReflectingHomomorphism A B f) :
    IsOriginalPartialHomomorphism A B f := by
  constructor
  · exact h.1
  · intro F x S hx
    simpa [hx] using (h.2 F x).symm

/-- A full embedding must also reflect the domain:
`none` in the source means `none` in the target. -/
structure Embedding (A : PartialSetStructure L V)
    (B : PartialSetStructure L W) where
  toFun : V → W
  injective : Function.Injective toFun
  map_rel_iff : ∀ R x, B.rel R (toFun ∘ x) ↔ A.rel R x
  map_func : ∀ F x, (A.func F x).map (Structure.imageSet toFun) =
    B.func F (toFun ∘ x)

/-- Closed sets contain ALL outputs of defined applications to
tuples within the set. Defined-empty tuples introduce no new
vertices, but retain their domain information. -/
def IsClosed (A : PartialSetStructure L V) (S : Set V) : Prop :=
  ∀ F x T, (∀ i, x i ∈ S) →
    A.func F x = some T → T ⊆ S

/-- Weak output restriction with the historical partial-map
convention:
  * undefined stays undefined;
  * originally defined-empty STAYS defined-empty;
  * nonempty outputs become restricted to surviving outputs;
  * if a previously nonempty output loses ALL its values, the
    restricted input becomes UNDEFINED, not defined-empty.

This is the useful vertex-exact weak operation for the iterated
partite proof. It must not be silently identified with ordinary
induced restriction of independent domain and graph relations. -/
noncomputable def weakValue (S : Set V) :
    Option (Set V) → Option (Set S)
  | none => none
  | some T => by
      classical
      exact
        if T.Nonempty then
          if (T ∩ S).Nonempty then
            some {y : S | y.1 ∈ T}
          else none
        else some ∅

noncomputable def weakInduce (A : PartialSetStructure L V)
    (S : Set V) : PartialSetStructure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := weakValue S (A.func F (Subtype.val ∘ x))

@[simp] theorem weakValue_none (S : Set V) :
    weakValue S (none : Option (Set V)) = none := rfl

/-- The originally defined empty value is NOT lost. -/
@[simp] theorem weakValue_some_empty (S : Set V) :
    weakValue S (some (∅ : Set V)) =
      some (∅ : Set S) := by
  simp [weakValue]

/-- A nonempty value whose whole image is outside the weak
carrier becomes UNDEFINED, not a defined-empty input. -/
theorem weakValue_nonempty_disjoint
    (S T : Set V) (hT : T.Nonempty)
    (hDisjoint : ¬ (T ∩ S).Nonempty) :
    weakValue S (some T) = none := by
  simp [weakValue, hT, hDisjoint]

/-- Collapse both `none` and `some ∅` to an empty fibre,
recovering the EXISTING survey/Lean representation while
irreversibly forgetting the independent domain bit. -/
def collapseDomain (A : PartialSetStructure L V) :
    Structure L V where
  rel := A.rel
  func F x := (A.func F x).getD ∅

/-- The legacy representation cannot distinguish the two
states. This example has one unary symbol and no relations. -/
def exampleLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity := fun _ => 1

def undefinedExample : PartialSetStructure exampleLanguage Unit where
  rel := fun R => Empty.elim R
  func := fun _ _ => none

def definedEmptyExample : PartialSetStructure exampleLanguage Unit where
  rel := fun R => Empty.elim R
  func := fun _ _ => some ∅

theorem example_distinct :
    undefinedExample ≠ definedEmptyExample := by
  intro h
  have hval := congrArg
    (fun A : PartialSetStructure exampleLanguage Unit =>
      A.func () (fun _ => ())) h
  change (none : Option (Set Unit)) = some ∅ at hval
  cases hval

theorem example_collapse_equal :
    collapseDomain undefinedExample =
      collapseDomain definedEmptyExample := rfl

/-- In the original partial sense an undefined source can map
to a target with a defined-empty input. -/
theorem undefined_to_definedEmpty_allowed :
    IsOriginalPartialHomomorphism
      undefinedExample definedEmptyExample id := by
  constructor
  · intro R
    exact Empty.elim R
  · intro F x T hx
    simp [undefinedExample] at hx

/-- Conversely a DEFINED-empty source must NOT map to an
undefined target. This is the information lost by the legacy
`Set V` fibre representation. -/
theorem definedEmpty_to_undefined_forbidden :
    ¬ IsOriginalPartialHomomorphism
      definedEmptyExample undefinedExample id := by
  intro h
  have hF := h.2 () (fun _ : Fin 1 => ()) (∅ : Set Unit) rfl
  change (none : Option (Set Unit)) =
    some (Structure.imageSet id (∅ : Set Unit)) at hF
  cases hF

end PartialSetStructure
end StructuralRamsey
