import PartiteConstruction.Ramsey.ClosureUSubstructurePreimage

/-! # The U-closure hull and U-size (2019, Definitions 2.22 and 2.25)

An ambient-relative U-substructure is a vertex set containing the outputs
of every existing U-closure tuple whose designated root lies in the set.

The U-closure of a set is the intersection of all U-substructures containing
it.  In particular this definition makes sense when the ambient structure
is only U-semi-closed.  On U-closed ambient structures, the resulting
induced hull is itself U-closed by Lemma 2.23(1).

The 2019 iterated partite construction measures the *minimum number of
generating vertices*, not the size of a generated hull.  U-size below is
that rank. It must not be used to replace weak projected image sets by
their generated closures during the vertex-exact image transfer.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V : Type v}

/-- The smallest U-substructure (relative to A) containing S, defined
as the intersection of all relative U-substructures containing S. -/
def UClosureHull (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) : Set V :=
  {x | ∀ T : Set V, IsUSubstructure rules A T → S ⊆ T → x ∈ T}

/-- The original generators belong to the closure hull. -/
theorem subset_UClosureHull
    (rules : ClosureDescription L) (A : RelStructure L V)
    (S : Set V) :
    S ⊆ UClosureHull rules A S := by
  intro x hx T _ hST
  exact hST hx

/-- Intersections of relative U-substructures remain relative
U-substructures. The hull is therefore U-closed *relative to A*. -/
theorem UClosureHull_isUSubstructure
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) :
    IsUSubstructure rules A (UClosureHull rules A S) := by
  intro rule hrule t ht hRoot j T hT hST
  exact hT rule hrule t ht
    (fun i => hRoot i T hT hST) j

/-- The closure hull is contained in any relative U-substructure
that contains its generators. -/
theorem UClosureHull_minimal
    (rules : ClosureDescription L)
    (A : RelStructure L V)
    {S T : Set V}
    (hT : IsUSubstructure rules A T) (hST : S ⊆ T) :
    UClosureHull rules A S ⊆ T := by
  intro x hx
  exact hx T hT hST

theorem UClosureHull_mono
    (rules : ClosureDescription L)
    (A : RelStructure L V) {S T : Set V}
    (hST : S ⊆ T) :
    UClosureHull rules A S ⊆ UClosureHull rules A T := by
  intro x hx Q hQ hTQ
  exact hx Q hQ (Set.Subset.trans hST hTQ)

/-- Relative U-closedness is exactly being fixed by the hull. -/
theorem UClosureHull_eq_iff
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) :
    UClosureHull rules A S = S ↔
      IsUSubstructure rules A S := by
  constructor
  · intro h
    rw [← h]
    exact UClosureHull_isUSubstructure rules A S
  · intro hS
    apply Set.Subset.antisymm
    · exact UClosureHull_minimal rules A hS (Set.Subset.rfl)
    · exact subset_UClosureHull rules A S

theorem UClosureHull_idempotent
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) :
    UClosureHull rules A (UClosureHull rules A S) =
      UClosureHull rules A S := by
  exact (UClosureHull_eq_iff rules A (UClosureHull rules A S)).2
    (UClosureHull_isUSubstructure rules A S)

/-- All vertices trivially generate the whole structure. -/
theorem UClosureHull_univ
    (rules : ClosureDescription L)
    (A : RelStructure L V) :
    UClosureHull rules A Set.univ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact subset_UClosureHull rules A Set.univ (Set.mem_univ x)

/-- In a fully U-closed ambient structure, the induced hull is
intrinsically U-closed, without enlarging any weak projected image. -/
theorem IsUClosed.induce_UClosureHull
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (hA : IsUClosed rules A) (S : Set V) :
    IsUClosed rules (A.induce (UClosureHull rules A S)) :=
  hA.induce_of_USubstructure (UClosureHull rules A S)
    (UClosureHull_isUSubstructure rules A S)

/-- A finite generating set is one whose U-closure contains every vertex. -/
def IsUGenerating
    (rules : ClosureDescription L)
    (A : RelStructure L V)
    (S : Set V) : Prop :=
  UClosureHull rules A S = Set.univ

/-- A finite structure has a generating set of some finite cardinality:
the entire vertex set.  No U-closedness of the ambient structure is needed. -/
theorem exists_UGenerating_card
    [Fintype V]
    (rules : ClosureDescription L)
    (A : RelStructure L V) :
    ∃ n : ℕ, ∃ S : Finset V,
      S.card = n ∧ IsUGenerating rules A (↑S : Set V) := by
  classical
  refine ⟨Fintype.card V, Finset.univ, ?_, ?_⟩
  · simp
  · simpa [IsUGenerating] using UClosureHull_univ rules A

/-- Published Definition 2.25: the number of vertices in a smallest
U-generating substructure. Distinct from the number of vertices in its
U-closure and from the cardinality of any arbitrary weak test. -/
noncomputable def USize
    [Fintype V]
    (rules : ClosureDescription L)
    (A : RelStructure L V) : ℕ := by
  classical
  exact Nat.find (exists_UGenerating_card rules A)

/-- A finite structure has a generating support attaining its U-size. -/
theorem USize_spec
    [Fintype V]
    (rules : ClosureDescription L)
    (A : RelStructure L V) :
    ∃ S : Finset V,
      S.card = USize rules A ∧
        IsUGenerating rules A (↑S : Set V) := by
  classical
  exact Nat.find_spec (exists_UGenerating_card rules A)

/-- U-size never exceeds the number of vertices. This bound does not
replace the original tested vertex set by a larger U-closure hull. -/
theorem USize_le_card
    [Fintype V]
    (rules : ClosureDescription L)
    (A : RelStructure L V) :
    USize rules A ≤ Fintype.card V := by
  classical
  obtain ⟨S, hCard, _⟩ := USize_spec rules A
  calc
    USize rules A = S.card := hCard.symm
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ S)
    _ = Fintype.card V := Finset.card_univ

end StructuralRamsey.RelStructure
