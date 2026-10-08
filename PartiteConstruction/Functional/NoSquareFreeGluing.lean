/-! # Bipartite 4-cycles in free unions

This is the combinatorial step underlying the obstruction to a generic
strict full-function tree target. If a bipartite relation is the union of
two relations supported on two sides, the two sides have no squares,
and their intersection contains at most one point of each role, then
the union has no square.

No claim about EHN canonical stages or tree-amalgam roots is hidden
in this lemma. Those geometric hypotheses have to be verified separately.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

universe v

/-- A square in a bipartite relation `E` with role predicates `X`
and `Y`, with all four vertices restricted to `S`. -/
def SquareFreeOn {V : Type v}
    (X Y S : V → Prop) (E : V → V → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂,
    X x₁ → X x₂ → Y y₁ → Y y₂ →
    x₁ ≠ x₂ → y₁ ≠ y₂ →
    E x₁ y₁ → E x₁ y₂ → E x₂ y₁ → E x₂ y₂ →
    S x₁ → S x₂ → S y₁ → S y₂ → False

/-- The square-free property survives a free union when the overlap has at
most one X-vertex and one Y-vertex. This uses no closure hull and applies
equally to the function-domain relation after any full free amalgam whose
gluing root has those cardinality bounds. -/
theorem squareFree_of_freeUnion
    {V : Type v}
    (X Y Left Right : V → Prop) (E : V → V → Prop)
    (hCover : ∀ z, Left z ∨ Right z)
    (hEdge : ∀ x y, E x y →
      (Left x ∧ Left y) ∨ (Right x ∧ Right y))
    (hXOverlap : ∀ x₁ x₂,
      X x₁ → X x₂ →
      Left x₁ → Right x₁ → Left x₂ → Right x₂ → x₁ = x₂)
    (hYOverlap : ∀ y₁ y₂,
      Y y₁ → Y y₂ →
      Left y₁ → Right y₁ → Left y₂ → Right y₂ → y₁ = y₂)
    (hLeft : SquareFreeOn X Y Left E)
    (hRight : SquareFreeOn X Y Right E) :
    SquareFreeOn X Y (fun _ => True) E := by
  intro x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
    h₁₁ h₁₂ h₂₁ h₂₂ _ _ _ _
  have leftNeighbor
      (x y : V) (hxy : E x y)
      (hL : Left x) (hR : ¬ Right x) : Left y := by
    rcases hEdge x y hxy with h | h
    · exact h.2
    · exact (hR h.1).elim
  have rightNeighbor
      (x y : V) (hxy : E x y)
      (hR : Right x) (hL : ¬ Left x) : Right y := by
    rcases hEdge x y hxy with h | h
    · exact (hL h.1).elim
    · exact h.2
  have exclusiveLeft
      (x x' : V)
      (hX : X x) (hX' : X x') (hxx' : x ≠ x')
      (he₁ : E x y₁) (he₂ : E x y₂)
      (he'₁ : E x' y₁) (he'₂ : E x' y₂)
      (hL : Left x) (hNotR : ¬ Right x) : False := by
    have hLy₁ : Left y₁ := leftNeighbor x y₁ he₁ hL hNotR
    have hLy₂ : Left y₂ := leftNeighbor x y₂ he₂ hL hNotR
    rcases hCover x' with hx'L | hx'R
    · exact hLeft x x' y₁ y₂ hX hX' hy₁ hy₂ hxx' hyy
        he₁ he₂ he'₁ he'₂ hL hx'L hLy₁ hLy₂
    · by_cases hx'L : Left x'
      · exact hLeft x x' y₁ y₂ hX hX' hy₁ hy₂ hxx' hyy
          he₁ he₂ he'₁ he'₂ hL hx'L hLy₁ hLy₂
      · have hRy₁ : Right y₁ :=
          rightNeighbor x' y₁ he'₁ hx'R hx'L
        have hRy₂ : Right y₂ :=
          rightNeighbor x' y₂ he'₂ hx'R hx'L
        exact hyy (hYOverlap y₁ y₂ hy₁ hy₂
          hLy₁ hRy₁ hLy₂ hRy₂)
  have exclusiveRight
      (x x' : V)
      (hX : X x) (hX' : X x') (hxx' : x ≠ x')
      (he₁ : E x y₁) (he₂ : E x y₂)
      (he'₁ : E x' y₁) (he'₂ : E x' y₂)
      (hR : Right x) (hNotL : ¬ Left x) : False := by
    have hRy₁ : Right y₁ := rightNeighbor x y₁ he₁ hR hNotL
    have hRy₂ : Right y₂ := rightNeighbor x y₂ he₂ hR hNotL
    rcases hCover x' with hx'L | hx'R
    · by_cases hx'R : Right x'
      · exact hRight x x' y₁ y₂ hX hX' hy₁ hy₂ hxx' hyy
          he₁ he₂ he'₁ he'₂ hR hx'R hRy₁ hRy₂
      · have hLy₁ : Left y₁ :=
          leftNeighbor x' y₁ he'₁ hx'L hx'R
        have hLy₂ : Left y₂ :=
          leftNeighbor x' y₂ he'₂ hx'L hx'R
        exact hyy (hYOverlap y₁ y₂ hy₁ hy₂
          hLy₁ hRy₁ hLy₂ hRy₂)
    · exact hRight x x' y₁ y₂ hX hX' hy₁ hy₂ hxx' hyy
        he₁ he₂ he'₁ he'₂ hR hx'R hRy₁ hRy₂
  by_cases hx₁L : Left x₁
  · by_cases hx₁R : Right x₁
    · rcases hCover x₂ with hx₂L | hx₂R
      · by_cases hx₂R : Right x₂
        · exact hxx (hXOverlap x₁ x₂ hx₁ hx₂
            hx₁L hx₁R hx₂L hx₂R)
        · exact exclusiveLeft x₂ x₁ hx₂ hx₁ hxx.symm
            h₂₁ h₂₂ h₁₁ h₁₂ hx₂L hx₂R
      · by_cases hx₂L : Left x₂
        · exact hxx (hXOverlap x₁ x₂ hx₁ hx₂
            hx₁L hx₁R hx₂L hx₂R)
        · exact exclusiveRight x₂ x₁ hx₂ hx₁ hxx.symm
            h₂₁ h₂₂ h₁₁ h₁₂ hx₂R hx₂L
    · exact exclusiveLeft x₁ x₂ hx₁ hx₂ hxx
        h₁₁ h₁₂ h₂₁ h₂₂ hx₁L hx₁R
  · have hx₁R : Right x₁ := (hCover x₁).resolve_left hx₁L
    exact exclusiveRight x₁ x₂ hx₁ hx₂ hxx
      h₁₁ h₁₂ h₂₁ h₂₂ hx₁R hx₁L

end StructuralRamsey.Structure.NativePowerObstruction
