import PartiteConstruction.Functional.FreeAmalgamGeneratorBudget

/-!
# An empty gluing separator contributes ZERO functional generators

A genuine full-functional free amalgam is a union of two CLOSED sides.
The standard generator-budget bound pays for the generators of the
whole source PLUS every vertex of the common root.

When the root is EMPTY, this extra budget disappears entirely:
an n-generated full free amalgam has BOTH sides n-generated.
This holds for functions of arbitrary arity; no unary restriction,
positive arity, projected rank hypothesis, or assumption about
A-copy histories is necessary. It also works for arbitrary relational
symbols, including nullaries, whenever a full free-amalgam diagram
exists.

An empty full functional structure is also irreducible in the
universal no-crossing definition: its embedded image lies in either
side vacuously. Combined with absolute strict side B-tree completions
and the irreducible-root synchronization theorem, these observations
remove the empty-separator case from the maximal mixed-root
extension problem of published Appendix A.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- Empty full function structures are irreducible for the exact
universal free-amalgamation notion. No finiteness or language
restriction is necessary. -/
theorem irreducible_of_isEmpty
    (Root : Structure L H) [IsEmpty H] :
    Root.Irreducible := by
  intro H' E' F' C' Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  left
  intro x
  exact isEmptyElim x

namespace IsFreeAmalgam

/-- For a genuine full-functional free amalgam OVER AN EMPTY ROOT,
the two sides inherit the same generator budget as the whole source.
In the general theorem each side costs an additional |Root|; here
|Root|=0, and no generated closure cardinality is involved. -/
theorem sides_generatedByAtMost_of_empty_root
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite H] [Finite E] [Finite F] [IsEmpty H]
    (hFree : IsFreeAmalgam sL sR iL iR)
    {n : ℕ} (hGen : Whole.GeneratedByAtMost n) :
    Left.GeneratedByAtMost n ∧ Right.GeneratedByAtMost n := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hZero : Nat.card H = 0 := by
    simp [Nat.card_eq_fintype_card]
  constructor
  · have h := hFree.left_generatedByAtMost_add_root hGen
    simpa [hZero] using h
  · have h := hFree.right_generatedByAtMost_add_root hGen
    simpa [hZero] using h

end IsFreeAmalgam
end StructuralRamsey.Structure
