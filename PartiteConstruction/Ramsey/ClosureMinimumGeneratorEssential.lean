import PartiteConstruction.Ramsey.ClosureWeakHullUSize

/-!
# Essential generators and closure-saturated proper cuts

The remaining closed-rank increment needs to construct a TRUE
proper free cut of a prescribed closed generated hull, not
merely of the exact weak generating set. Saturating a proposed
weak side by U-closure can absorb vertices from the opposite
side unless an excluded generator is provably not generated.

Here is the basic valid observation: every member x of a
MINIMUM U-generating support G is essential:

    x ∉ cl_U(G\{x}).

Indeed, if the smaller support generated x, its ambient hull
would contain G and hence the whole structure, contradicting
the cardinal minimality of G.

More generally, if a candidate source-side seed S is
CONTAINED in cl_U(G\{x}), then its ambient U-closure still
omits x. This is the exact sufficient condition needed
to ensure that saturating a proposed side does not destroy
properness by swallowing its excluded generator.

Crucial limitation: arbitrary core/rest vertex sets in the
temporarily non-semi-closed HJ Picture need not be contained
in the closure of the surviving generators. A vertex outside
G may have been generated using x and may in turn generate x.
The actual-history containment is STILL UNPROVED, as is the
full repaired closed rank j→j+1 completion step.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Every member of a minimum generating set is genuinely
U-essential. No U-closedness of the ambient structure is
required, and the result uses the intrinsic relative closure
operator on the exact ambient carrier. -/
theorem minimum_generator_not_in_erase_hull
    [Fintype V] [DecidableEq V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (G : Finset V)
    (hGen : IsUGenerating rules A (↑G : Set V))
    (hMin : G.card = USize rules A)
    (x : V) (hx : x ∈ G) :
    x ∉ UClosureHull rules A (↑(G.erase x) : Set V) := by
  classical
  intro hxHull
  let H : Set V := UClosureHull rules A (↑(G.erase x) : Set V)
  have hHClosed : IsUSubstructure rules A H :=
    UClosureHull_isUSubstructure rules A (↑(G.erase x) : Set V)
  have hGsubset : (↑G : Set V) ⊆ H := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      exact hxHull
    · exact subset_UClosureHull rules A
        (↑(G.erase x) : Set V)
        (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  have hEGen : IsUGenerating rules A
      (↑(G.erase x) : Set V) := by
    change H = Set.univ
    apply Set.eq_univ_of_forall
    intro y
    have hGenHull : y ∈
        UClosureHull rules A (↑G : Set V) := by
      rw [hGen]
      trivial
    exact UClosureHull_minimal rules A hHClosed
      hGsubset hGenHull
  have hBound : USize rules A ≤ (G.erase x).card :=
    USize_le_of_generating rules A (G.erase x) hEGen
  have hPos : 0 < G.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hErase : (G.erase x).card = G.card - 1 :=
    Finset.card_erase_of_mem hx
  omega

/-- Closure saturation of any seed already contained in the
hull of the OTHER minimum generators remains proper: it
cannot absorb their missing essential generator. -/
theorem minimum_generator_excluded_from_saturated_side
    [Fintype V] [DecidableEq V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (G : Finset V)
    (hGen : IsUGenerating rules A (↑G : Set V))
    (hMin : G.card = USize rules A)
    (x : V) (hx : x ∈ G)
    (S : Set V)
    (hSeed : S ⊆ UClosureHull rules A (↑(G.erase x) : Set V)) :
    x ∉ UClosureHull rules A S := by
  intro hxS
  have hHull : IsUSubstructure rules A
      (UClosureHull rules A (↑(G.erase x) : Set V)) :=
    UClosureHull_isUSubstructure rules A (↑(G.erase x) : Set V)
  have hIncluded : UClosureHull rules A S ⊆
      UClosureHull rules A (↑(G.erase x) : Set V) :=
    UClosureHull_minimal rules A hHull hSeed
  exact minimum_generator_not_in_erase_hull
    rules A G hGen hMin x hx (hIncluded hxS)

end StructuralRamsey.RelStructure
