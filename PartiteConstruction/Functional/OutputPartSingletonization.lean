import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.SingletonExpansion

/-!
# Split transversal multivalued functions into canonical singleton output parts

For every genuine functional partite system B with part map p:V→P,
replace each primitive function symbol F with symbols (F,q) indexed
by actual output part q∈P. The (F,q) fibre contains precisely the
original F-values in the part q.

Each such fibre is empty or a singleton because B.funcTransversal
holds. The original multivalued function is recovered by taking the
union of these singleton fibres over all q, with NO linear ordering,
ranking, new vertex, closure hull, or change to the original part map.

The construction is a full-embedding-compatible presentation of
the same native function-language partite systems, not a new
relational Ramsey Picture. It is the entry point to applying
singleton-valued 2019 U-closure rules to MULTIVALUED functional
partite stages.
-/

namespace StructuralRamsey

universe u v w z

namespace Language

/-- A canonical SINGLETON function symbol (F,q) for every
original function symbol F and output part q. Relation symbols
and argument arities are unchanged. The language universe
allows the possibly larger type of part labels P. -/
def outputPartIndexed (L : Language.{u}) (P : Type v) :
    Language.{max u v} where
  RelSymbol := ULift.{max u v, u} L.RelSymbol
  FuncSymbol := ULift.{max u v, u} L.FuncSymbol × P
  relArity := fun R => L.relArity R.down
  funcArity := fun Fq => L.funcArity Fq.1.down

end Language

namespace FunctionalPartite

open Structure

variable {L : Language.{u}} {P : Type v} {V : Type w} {W : Type z}

/-- The CANONICAL per-output-part singleton representation of
a genuine set-valued functional partite system.

It lives on the EXACT same vertices and uses the SAME
original part map. All original relations are unchanged. -/
def System.splitOutputParts (B : System L P V) :
    System (L.outputPartIndexed P) P V where
  toStructure := {
    rel := fun R xs => B.rel R.down xs
    func := fun Fq xs =>
      {y | y ∈ B.func Fq.1.down xs ∧ B.part y = Fq.2}
  }
  part := B.part
  relTransversal := by
    intro R xs hx i j heq
    exact B.relTransversal R.down xs hx i j heq
  funcTransversal := by
    intro Fq xs y z hy hz _hPart
    exact B.funcTransversal Fq.1.down xs y z hy.1 hz.1
      (hy.2.trans hz.2.symm)

/-- Every output-part fibre of the split is singleton-valued.
This does NOT assume the original function has only one value:
distinct original values may lie in DIFFERENT parts. -/
theorem System.splitOutputParts_singletonValued
    (B : System L P V) :
    (B.splitOutputParts).toStructure.SingletonValued := by
  intro Fq xs y z hy hz
  exact B.funcTransversal Fq.1.down xs y z hy.1 hz.1
    (hy.2.trans hz.2.symm)

/-- The split (F,q) fibre is EXACTLY the set of original F values
whose part is q. This is literal fibre equality, not merely
a preservation-of-nonemptiness assertion. -/
theorem System.mem_splitOutputParts_iff
    (B : System L P V) (F : L.FuncSymbol) (q : P)
    (xs : Fin (L.funcArity F) → V) (y : V) :
    y ∈ (B.splitOutputParts).func ((ULift.up F : ULift.{max u v, u} L.FuncSymbol),q) xs ↔
      y ∈ B.func F xs ∧ B.part y = q :=
  Iff.rfl

/-- Every ORIGINAL multivalued output is recovered from its
UNIQUE actual output-part singleton fibre, with no loss or
addition of any original value. -/
theorem System.mem_original_iff_split_actualPart
    (B : System L P V) (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) (y : V) :
    y ∈ B.func F xs ↔
      y ∈ (B.splitOutputParts).func (ULift.up F,B.part y) xs := by
  constructor
  · intro hy
    exact ⟨hy, rfl⟩
  · exact And.left

/-- Native function-closed subsets are EXACTLY those closed under
ALL canonical output-part singleton operations, on the same
underlying vertex set. This is the genuine multivalued
functional analogue of relative 2019 U-closedness. -/
theorem System.isClosed_iff_splitOutputParts_isClosed
    (B : System L P V) (S : Set V) :
    B.toStructure.IsClosed S ↔
      (B.splitOutputParts).toStructure.IsClosed S := by
  constructor
  · intro hClosed Fq xs hxs y hy
    exact hClosed Fq.1.down xs hxs hy.1
  · intro hClosed F xs hxs y hy
    exact hClosed (ULift.up F, B.part y) xs hxs ⟨hy, rfl⟩

namespace Embedding

variable {A : System L P V} {B : System L P W}

/-- Genuine FULL PART-PRESERVING native function embeddings
remain FULL primitive function embeddings after canonical
output-part singletonization.

Both directions of complete function-fibre equality use
the genuine full source function map and preservation of
output part labels; a merely weak EHN projection is NOT
eligible for this theorem. -/
def splitOutputParts (e : Embedding A B) :
    Embedding A.splitOutputParts B.splitOutputParts where
  toEmbedding := {
    toFun := e
    injective := e.toEmbedding.injective
    map_rel_iff := fun R xs => e.toEmbedding.map_rel_iff R.down xs
    map_func := by
      intro Fq xs
      rcases Fq with ⟨F, q⟩
      change imageSet e
          {z : V | z ∈ A.func F.down xs ∧ A.part z = q} =
        {y : W | y ∈ B.func F.down (e ∘ xs) ∧ B.part y = q}
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hzPart⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← e.toEmbedding.map_func F.down xs]
          exact ⟨z, hz, rfl⟩
        · exact (e.map_part z).trans hzPart
      · rintro ⟨hy, hq⟩
        rw [← e.toEmbedding.map_func F.down xs] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        have hpart : A.part z = q := by
          calc
            A.part z = B.part (e z) := (e.map_part z).symm
            _ = B.part y := congrArg B.part hzy
            _ = q := hq
        exact ⟨z, ⟨hz, hpart⟩, hzy⟩
  }
  map_part := e.map_part

end Embedding

/-- Canonical per-part singletonization preserves the precise
SURVIVING output incidences of every arbitrary exact WEAK
functional test.

Both presentations retain only original values whose vertices
actually belong to S, and nothing from a generated closure.
AMBIENT active domains remain separate data when applying
the 2019 tagged U-root induction. -/
theorem System.splitOutputParts_weak_func_iff
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol) (q : P)
    (xs : Fin (L.funcArity F) → S) (y : S) :
    y ∈ ((B.splitOutputParts).toStructure.weakInduce S).func
      ((ULift.up F : ULift.{max u v, u} L.FuncSymbol), q) xs ↔
      y ∈ (B.toStructure.weakInduce S).func F xs ∧
        B.part y.1 = q :=
  Iff.rfl

end FunctionalPartite
end StructuralRamsey
