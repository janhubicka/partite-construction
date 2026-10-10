import PartiteConstruction.Ramsey.ClosureDisjointLineOverlap

/-!
# Two actual transverse HJ lines factor their common vertices
# through a PAIR of old A-letters

The pairwise overlap theorem #207 identifies a canonical A-word
containing every common vertex of two native parameter lines.
For the rank step we need more: the inverse old-picture
coordinates of the two line embeddings must factor through a
SINGLE abstract A-part in two potentially DIFFERENT embeddings.

If W,W' have disjoint parameter-coordinate sets, take a variable
coordinate k of W and a variable coordinate l of W'. Then W'
has a constant letter e at k, and W has a constant letter d at
l. Equality lineMap(W,x)=lineMap(W',y) forces

    part(x)=part(y),    x=e(part(x)),    y=d(part(y)).

Thus a common source root in the intersection of TWO attached
old copies factors through q:Root->A given by its parts and the
two induced full embeddings e,d:A->Old. This is the precise
boundary compatibility data requested by the conditional two-side
completion criterion (PR #217). It does not claim that the
whole mixed test lies inside the two copies (arbitrary core
vertices can exist), or that the boundary has zero U-rank cost.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P V : Type v} {N : ℕ}

/-- The two PREIMAGES of a common vertex of genuine transverse
native lines are the images of their common part under two
explicit A-letters. This is stronger than merely locating
the common core vertex inside a word copy. -/
theorem transverse_lines_common_preimages_are_letters
    (A : RelStructure L P) (B : System L P V)
    (W W' : Line (Letter A B) N)
    (hDisjoint : ∀ k : Fin N,
      W.symbol k = .parameter → W'.symbol k ≠ .parameter) :
    ∃ (e d : Letter A B), ∀ x y : V,
      NonInduced.lineMap W x = NonInduced.lineMap W' y →
      B.part x = B.part y ∧
        x = e (B.part x) ∧ y = d (B.part y) := by
  obtain ⟨k, hk⟩ := W.hasParameter
  obtain ⟨l, hl⟩ := W'.hasParameter
  cases hW'k : W'.symbol k with
  | parameter =>
      exact False.elim (hDisjoint k hk hW'k)
  | const e =>
      cases hWl : W.symbol l with
      | parameter =>
          exact False.elim (hDisjoint l hWl hl)
      | const d =>
          refine ⟨e, d, ?_⟩
          intro x y hxy
          have hParts : B.part x = B.part y :=
            congrArg (fun z : Vertex B N => z.part) hxy
          have hX : x = e (B.part y) := by
            have hcoord :=
              congrArg (fun z : Vertex B N => z.coord k) hxy
            simpa only [NonInduced.lineMap, hk, hW'k] using hcoord
          have hY : y = d (B.part x) := by
            have hcoord :=
              congrArg (fun z : Vertex B N => z.coord l) hxy
            have hdy : d (B.part x) = y := by
              simpa only [NonInduced.lineMap, hWl, hl] using hcoord
            exact hdy.symm
          refine ⟨hParts, ?_, ?_⟩
          · exact hX.trans (congrArg e hParts.symm)
          · exact hY.trans (congrArg d hParts)

/-- The pair of actual old preimage maps over any common root
factors through one abstract part map q:Root->A, even if q
is noninjective and the root is nonclosed. The two copies of A
in Old may differ, as expected in a no-common-coordinate case. -/
theorem transverse_lines_compatible_root_parts
    (A : RelStructure L P) (B : System L P V)
    (W W' : Line (Letter A B) N)
    (hDisjoint : ∀ k : Fin N,
      W.symbol k = .parameter → W'.symbol k ≠ .parameter)
    {H : Type v} (x y : H → V)
    (hSame : ∀ r : H,
      NonInduced.lineMap W (x r) =
        NonInduced.lineMap W' (y r)) :
    ∃ (e d : Letter A B) (q : H → P),
      (∀ r, x r = e (q r)) ∧
      (∀ r, y r = d (q r)) := by
  obtain ⟨e, d, he⟩ :=
    transverse_lines_common_preimages_are_letters A B W W' hDisjoint
  let q : H → P := fun r => B.part (x r)
  refine ⟨e, d, q, ?_, ?_⟩
  · intro r
    exact (he (x r) (y r) (hSame r)).2.1
  · intro r
    obtain ⟨hParts, _, hY⟩ := he (x r) (y r) (hSame r)
    exact hY.trans (congrArg d hParts.symm)

end StructuralRamsey.Partite.Induced
