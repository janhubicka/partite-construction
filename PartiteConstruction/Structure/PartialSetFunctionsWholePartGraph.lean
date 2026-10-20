import PartiteConstruction.Structure.PartialSetFunctionsWholeGraph
import PartiteConstruction.Structure.PartialSetFunctionsTransversal

/-!
# Finite complete-value output-part tuples

In a finite partite system with transversal function values, each defined
value is described by a tuple indexed by distinct output parts. The number
of slots is bounded by the finite number of parts. Keeping one WHOLE value
tuple (rather than separate output incidences) makes restriction to an exact
weak vertex set commute with relational induction.

The present result is a finite *source language* and a pointwise uniqueness
lemma. A full 2019 U-closure description still needs the distinct-input
equality patterns, full induced old root patterns, and explicit active-root
domain relations. In particular do not infer target-tree completion here.
-/

namespace StructuralRamsey

universe u v w

namespace Language

/-- A finite list of pairwise distinct output parts, with width bounded by
the number of available parts. The chosen order is part of the symbol. -/
abbrev CompleteOutputParts (P : Type v) [Fintype P] :=
  { q : (Σ n : Fin (Fintype.card P + 1), Fin n.val → P) //
      Function.Injective q.2 }

namespace CompleteOutputParts

variable {P : Type v} [Fintype P]

def size (q : CompleteOutputParts P) : ℕ := q.1.1.val

def label (q : CompleteOutputParts P) : Fin q.size → P := q.1.2

theorem label_injective (q : CompleteOutputParts P) :
    Function.Injective q.label := q.2

instance : Finite (CompleteOutputParts P) := by
  classical
  unfold CompleteOutputParts
  infer_instance

end CompleteOutputParts

/-- Finite signature containing a relation symbol for every original
relation and every complete output-part tuple of a primitive function. -/
def completeOutputPartLanguage (L : Language.{u}) (P : Type v)
    [Fintype P] : RelLanguage.{max u v} where
  Symbol := L.RelSymbol ⊕ (L.FuncSymbol × CompleteOutputParts P)
  arity
    | .inl R => L.relArity R
    | .inr (F, q) => L.funcArity F + q.size

instance completeOutputPartLanguage_symbol_finite
    (L : Language.{u}) (P : Type v) [Fintype P]
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (completeOutputPartLanguage L P).Symbol := by
  change Finite (L.RelSymbol ⊕ (L.FuncSymbol × CompleteOutputParts P))
  infer_instance

end Language

namespace PartialSetStructure

variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Record a COMPLETE defined value as one tuple. Each output coordinate
is assigned its distinct part by the relation symbol. The zero-width
symbol records a defined-empty application, not an undefined input. -/
def completeOutputPartGraph (A : PartialSetStructure L V) (part : V → P) :
    RelStructure (Language.completeOutputPartLanguage L P) V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr (F, q), xs =>
        A.func F (fun i => xs (Fin.castAdd q.size i)) =
          some (Set.range (fun j : Fin q.size =>
            xs (Fin.natAdd (L.funcArity F) j))) ∧
        ∀ j : Fin q.size,
          part (xs (Fin.natAdd (L.funcArity F) j)) = q.label j

/-- Restriction of every complete-value relation is literally induced
restriction on the SAME weak carrier. No fibre can be partially clipped. -/
theorem wholeWeakInduce_completeOutputPartGraph_rel_iff
    (A : PartialSetStructure L V) (part : V → P) (S : Set V)
    (R : (Language.completeOutputPartLanguage L P).Symbol)
    (xs : Fin ((Language.completeOutputPartLanguage L P).arity R) → S) :
    (completeOutputPartGraph (wholeWeakInduce A S)
      (part ∘ Subtype.val)).rel R xs ↔
      ((completeOutputPartGraph A part).induce S).rel R xs := by
  cases R with
  | inl R => rfl
  | inr Fq =>
      rcases Fq with ⟨F, q⟩
      change
        (wholeWeakValue S
            (A.func F (fun i => (xs (Fin.castAdd q.size i)).1)) =
            some (Set.range (fun j : Fin q.size =>
              xs (Fin.natAdd (L.funcArity F) j))) ∧
          ∀ j : Fin q.size,
            part (xs (Fin.natAdd (L.funcArity F) j)).1 = q.label j) ↔
        (A.func F (fun i => (xs (Fin.castAdd q.size i)).1) =
            some (Set.range (fun j : Fin q.size =>
              (xs (Fin.natAdd (L.funcArity F) j)).1)) ∧
          ∀ j : Fin q.size,
            part (xs (Fin.natAdd (L.funcArity F) j)).1 = q.label j)
      exact and_congr
        (wholeWeakValue_eq_some_range_iff S
          (A.func F (fun i => (xs (Fin.castAdd q.size i)).1))
          (fun j : Fin q.size => xs (Fin.natAdd (L.funcArity F) j)))
        Iff.rfl

/-- The identity is a full embedding in either direction between the
complete-value graph of a whole-weak test and its ambient induced graph. -/
def wholeWeakCompletePartGraphToInduce
    (A : PartialSetStructure L V) (part : V → P) (S : Set V) :
    RelStructure.Embedding
      (completeOutputPartGraph (wholeWeakInduce A S)
        (part ∘ Subtype.val))
      ((completeOutputPartGraph A part).induce S) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    exact (wholeWeakInduce_completeOutputPartGraph_rel_iff
      A part S R xs).symm

/-- For fixed input and fixed output-part tuple, transversality forces
every output coordinate to be unique. This also permits output vertices
which coincide with input vertices. -/
theorem completeOutputPartGraph_unique_outputs
    (A : PartialSetStructure L V) (part : V → P)
    (hTrans : FibreTransversal A part)
    (F : L.FuncSymbol) (q : Language.CompleteOutputParts P)
    (xs ys : Fin (L.funcArity F + q.size) → V)
    (hxs : (completeOutputPartGraph A part).rel (.inr (F, q)) xs)
    (hys : (completeOutputPartGraph A part).rel (.inr (F, q)) ys)
    (hRoot : ∀ i : Fin (L.funcArity F),
      xs (Fin.castAdd q.size i) = ys (Fin.castAdd q.size i)) :
    ∀ j : Fin q.size,
      xs (Fin.natAdd (L.funcArity F) j) =
        ys (Fin.natAdd (L.funcArity F) j) := by
  let inX : Fin (L.funcArity F) → V :=
    fun i => xs (Fin.castAdd q.size i)
  let inY : Fin (L.funcArity F) → V :=
    fun i => ys (Fin.castAdd q.size i)
  let outX : Fin q.size → V :=
    fun j => xs (Fin.natAdd (L.funcArity F) j)
  let outY : Fin q.size → V :=
    fun j => ys (Fin.natAdd (L.funcArity F) j)
  have hInput : inX = inY := funext hRoot
  have hValX : A.func F inX = some (Set.range outX) := hxs.1
  have hValY : A.func F inY = some (Set.range outY) := hys.1
  have hSets : Set.range outX = Set.range outY :=
    Option.some.inj
      (hValX.symm.trans ((congrArg (A.func F) hInput).trans hValY))
  intro j
  have hx : outX j ∈ Set.range outX := ⟨j, rfl⟩
  have hy : outY j ∈ Set.range outX := by
    rw [hSets]
    exact ⟨j, rfl⟩
  have hp : part (outX j) = part (outY j) :=
    (hxs.2 j).trans (hys.2 j).symm
  exact hTrans F inX (Set.range outX) hValX (outX j) hx (outY j) hy hp

end PartialSetStructure
end StructuralRamsey
