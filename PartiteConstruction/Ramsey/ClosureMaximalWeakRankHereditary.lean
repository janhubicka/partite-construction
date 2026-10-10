import PartiteConstruction.Ramsey.ClosureMaximalWeakRank
import PartiteConstruction.Ramsey.ClosureRelativeSideRange

/-!
# Maximal weak U-rank is hereditary to ALL induced weak sides

Merged #211 proves that a finite weak structure of maximal U-size has
every exact subset relatively U-closed. This file proves the missing
converse and inheritance:

* If every exact subset is a relative U-substructure, a generating
  subset must be the WHOLE carrier, so USize = |carrier|.
* If every subset of A is relatively U-closed, then every subset of
  an arbitrary induced weak side A|T is relatively U-closed as well.
* Consequently EVERY induced side of a finite maximal-U-rank weak test
  is also maximal rank, and an ORDINARY relational homomorphism-
  embedding out of that side automatically protects all CLOSED
  U-irreducible tests by #211.

In particular, the actual core/copy/rest pieces in the proper
free decompositions from merged #218 inherit this stronger property.
This allows the native ORDINARY coordinate retractions (draft #216)
to qualify as corrected protected maps whenever a piece is an
induced portion of a maximal-rank weak test.

This does not itself construct the target boundary q:Root->Q or show
that every mixed Hales--Jewett history can be split into two pieces
with root-compatible coordinate retractions. The full j->j+1
completion increment remains unproved.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W : Type v}

/-- Any exact weak induced portion of a structure in which ALL
subsets are relatively U-closed retains the same property.
No closedness of either ambient structure or portion is assumed. -/
theorem all_subsets_relative_induce
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hAll : ∀ S : Set V, IsUSubstructure rules A S)
    (T : Set V) :
    ∀ R : Set T, IsUSubstructure rules (A.induce T) R := by
  intro R rule hrule t ht hRoot j
  have htA : A.rel rule.symbol (Subtype.val ∘ t) := ht
  have hRootA : ∀ i : Fin rule.rootSize,
      (Subtype.val ∘ t) (i.castLE rule.rootLE) ∈
        Subtype.val '' R := by
    intro i
    exact ⟨t (i.castLE rule.rootLE), hRoot i, rfl⟩
  obtain ⟨x, hx, heq⟩ :=
    (hAll (Subtype.val '' R)) rule hrule
      (Subtype.val ∘ t) htA hRootA j
  have hxEq : x = t j := Subtype.ext heq
  simpa only [hxEq] using hx

/-- The converse to maximal-rank independence (#211):
if every subset is relatively U-closed, no proper subset can
generate the whole weak structure. -/
theorem USize_eq_card_of_all_subsets_relative
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hAll : ∀ S : Set V, IsUSubstructure rules A S) :
    USize rules A = Fintype.card V := by
  classical
  obtain ⟨G, hCard, hGen⟩ := USize_spec rules A
  have hHull : UClosureHull rules A (↑G : Set V) ⊆ (↑G : Set V) :=
    UClosureHull_minimal rules A (hAll (↑G : Set V))
      (Set.Subset.rfl)
  have hGAll : G = Finset.univ := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      have hx : x ∈ UClosureHull rules A (↑G : Set V) := by
        rw [hGen]
        trivial
      exact hHull hx
  calc
    USize rules A = G.card := hCard.symm
    _ = (Finset.univ : Finset V).card :=
      congrArg Finset.card hGAll
    _ = Fintype.card V := Finset.card_univ

/-- Every induced weak side of any FINITE maximal-U-rank test also
has maximal intrinsic U-size. This is stronger than mere relative
closedness of the side range in the parent. -/
theorem induced_USize_eq_card_of_max_USize
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hMax : USize rules A = Fintype.card V)
    (T : Set V) [Fintype T] :
    USize rules (A.induce T) = Fintype.card T :=
  USize_eq_card_of_all_subsets_relative rules (A.induce T)
    (all_subsets_relative_induce rules A
      (all_subsets_relative_of_USize_eq_card rules A hMax) T)

/-- Ordinary coordinate homomorphism-embeddings on arbitrary exact
induced sides of a maximal-U-rank weak source are automatically
working protected closed-test maps. The ambient source need not be
closed, and neither side's set of vertices is enlarged. -/
theorem IsHomomorphismEmbedding.toClosedMap_induced_of_max_USize
    [Fintype V]
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (hMax : USize rules A = Fintype.card V)
    (T : Set V) [Fintype T]
    (f : T → W)
    (hf : (A.induce T).IsHomomorphismEmbedding B f) :
    IsClosedUHomomorphismEmbedding rules (A.induce T) B f :=
  hf.toClosedMap_of_max_USize
    (induced_USize_eq_card_of_max_USize rules A hMax T)

end StructuralRamsey.RelStructure
