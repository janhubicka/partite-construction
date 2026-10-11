import PartiteConstruction.Ramsey.ClosureMaximalWeakOrdinarySides
import PartiteConstruction.Ramsey.ClosureGeneratedABoundary

/-!
# Two ordinary side maps with a generated A-boundary

A precise combined interface for the unresolved transverse native
Hales--Jewett case.

Suppose an exact weak Whole has maximal intrinsic U-size, is a free
amalgam of Left and Right, and both sides have at most j vertices.
Suppose there are two (generally DIFFERENT) ORDINARY relational
homomorphism-embeddings to a single old U-closed picture D, whose
source-root images factor through two induced embeddings of the
SAME selected U-closed A∈K.

Then Whole has a corrected K-completion, assuming the previous
closed rank-j completion invariant in D and strong amalgamation of K.

No U-closedness of the weak source/sides/root is required, and
neither protection of side maps nor membership of a pre-existing
closed boundary Q is postulated. Both are DERIVED: maximal
U-rank makes side maps protected on closed tests, and the
closure of the root-part image inside A is the shared closed
K-member Q.

What remains UNPROVED is the ACTUAL native-history assertion
that every transverse multi-line closed rank-j+1 test produces
such a proper free cut with two compatible ordinary projections.
This lemma must not be substituted for that history argument.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C V P : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E}
variable {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {D : RelStructure L V}
variable {A : RelStructure L P}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}

/-- Complete a maximal-rank weak free source from two distinct
ORDINARY small-side maps agreeing over two induced A-copies.
The old rank-j hypothesis applies to closed hulls of the entire
projected side images, which have at most j generators.
The K boundary is constructed from the image of the source root
inside A; it is not charged again to either side's support. -/
theorem HasClosedUKCompletion.of_maximal_weak_two_ordinary_side_maps_via_A
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    [Fintype C] [Fintype E] [Fintype F]
    [Finite V] [Finite P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hDClosed : IsUClosed rules D)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (q : H → P)
    (pL : E → V) (pR : F → V)
    (hpL : Left.IsHomomorphismEmbedding D pL)
    (hpR : Right.IsHomomorphismEmbedding D pR)
    (aL aR : Embedding A D)
    (hRootL : ∀ r : H, pL (sL r) = aL (q r))
    (hRootR : ∀ r : H, pR (sR r) = aR (q r))
    (j : ℕ)
    (hCardL : Fintype.card E ≤ j)
    (hCardR : Fintype.card F ≤ j)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules Whole := by
  have hAll : ∀ S : Set C, IsUSubstructure rules Whole S :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
  have hMaxL : USize rules Left = Fintype.card E :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iL
  have hMaxR : USize rules Right = Fintype.card F :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iR
  have hProtectedL : IsClosedUHomomorphismEmbedding rules Left D pL :=
    hpL.toClosedMap_of_max_USize hMaxL
  have hProtectedR : IsClosedUHomomorphismEmbedding rules Right D pR :=
    hpR.toClosedMap_of_max_USize hMaxR
  exact HasClosedUKCompletion.of_two_small_side_projections_via_A
    rules hK hHer hKIrr hSrc
    (hAll (Set.range iL)) (hAll (Set.range iR))
    hDClosed hAK hAClosed
    q pL pR hProtectedL hProtectedR aL aR hRootL hRootR
    j hCardL hCardR hRank

end StructuralRamsey.RelStructure
