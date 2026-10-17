import PartiteConstruction.Functional.WeakPatternDomainBridge2019

/-!
# Coherent active functional U-roots across genuine FULL attaching maps

For a genuine partite functional system and a fixed operation input,
the Boolean predicate ActiveOutputAtPart(F, xs, q) records the
existence of a value in output part q. Every fibre is transversal:
such a value, if present, is UNIQUE.

FULL partite embeddings reflect the ENTIRE fibre and preserve its
part labelling, so they preserve-and-reflect every active output-part
bit. In a genuine FULL functional free attachment, the same closed
support Root is embedded fully into both sides, hence the two sides
have exactly the same ambient active-output masks on every root tuple.

This is the direct functional counterpart of equality of active
U-closure roots on one true common closed boundary. A WEAK EHN
projection need not reflect newly defined target roots, so no
corresponding biconditional is claimed for arbitrary projections.

The ROOT MASKS are coherent; the missing mathematical lemma of the
iterated strict functional sparsening theorem is still a compatible
choice of relative TARGET strict B-tree root-completion profiles.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V W H : Type v}

/-- An ambient function application has an output in the specified
part. The true partite transversality axiom makes that output unique
when it exists, turning this predicate into one canonical singleton
closure slot of the enriched U-style representation. -/
def System.ActiveOutputAtPart (B : System L P V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (q : P) : Prop :=
  ∃ y : V, y ∈ B.func F xs ∧ B.part y = q

/-- FULL functional partite embeddings transport each output-part
closure-root bit in BOTH directions. No singleton-valuedness is
required; arbitrary multivalued fibres are supported. -/
theorem Embedding.activeOutputAtPart_iff
    {A : System L P V} {B : System L P W}
    (f : Embedding A B)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (q : P) :
    A.ActiveOutputAtPart F xs q ↔
      B.ActiveOutputAtPart F (f ∘ xs) q := by
  constructor
  · rintro ⟨y, hy, hq⟩
    refine ⟨f y, ?_, ?_⟩
    · rw [← f.map_func F xs]
      exact ⟨y, hy, rfl⟩
    · exact (f.map_part y).trans hq
  · rintro ⟨z, hz, hq⟩
    have hImage :
        z ∈ Structure.imageSet f (A.func F xs) := by
      rw [f.map_func F xs]
      exact hz
    obtain ⟨y, hy, hEq⟩ := hImage
    refine ⟨y, hy, ?_⟩
    calc
      A.part y = B.part (f y) := (f.map_part y).symm
      _ = B.part z := congrArg B.part hEq
      _ = q := hq

/-- On the SAME actual full functional attaching root, the ambient
active-output mask agrees on both sides, including masks whose
actual output vertices are omitted by an arbitrary WEAK test.

This statement is unconditional once the two attaching root maps
are genuine FULL partite embeddings, as they are in the native
Hales-Jewett Picture. -/
theorem System.activeOutputAtPart_commonRoot_iff
    (Root : System L P H)
    (Left : System L P V) (Right : System L P W)
    (iLeft : Embedding Root Left)
    (iRight : Embedding Root Right)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → H)
    (q : P) :
    Left.ActiveOutputAtPart F (iLeft ∘ xs) q ↔
      Right.ActiveOutputAtPart F (iRight ∘ xs) q := by
  exact (iLeft.activeOutputAtPart_iff F xs q).symm.trans
    (iRight.activeOutputAtPart_iff F xs q)

/-- The part of a function fibre that is active at a given output
part is a singleton when nonempty, even in multivalued systems. -/
theorem System.activeOutputAtPart_unique
    (B : System L P V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
    (q : P)
    (hActive : B.ActiveOutputAtPart F xs q) :
    ∃! y : V, y ∈ B.func F xs ∧ B.part y = q :=
  B.existsUnique_output_at_part F xs q hActive

end StructuralRamsey.FunctionalPartite
