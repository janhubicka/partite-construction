import PartiteConstruction.Ramsey.ClosureMaximalWeakRankHereditary
import PartiteConstruction.Ramsey.ClosureTwoSideSmallProjection

/-!
# Gluing maximal weak free cuts from ORDINARY side projections

At a Hales--Jewett multi-line attachment, the coordinate evaluation
maps into the previous old picture are generally only ordinary
relational homomorphism-embeddings. Requiring them to be globally
protected closed-test maps would hide part of the induction.

A finite source with maximal intrinsic U-rank has ALL vertex subsets
relatively U-closed. An ordinary full embedding of ANY weak
substructure into that source pulls this property back: the
substructure itself has maximal U-rank. Thus an ORDINARY
homomorphism-embedding out of either side of a proper free cut is
automatically a protected closed-test map, by #211.

The checked theorem
  HasClosedUKCompletion.of_two_small_side_projections
then glues independently completed projected side hulls through one
generated closed K-boundary Q, with potentially DIFFERENT Q->D
embeddings on the two sides. Here that theorem is instantiated
without assuming protected side maps or relative U-closedness
of the side ranges: both are derived from the maximal-rank
condition on the WHOLE exact weak source.

This is a conditional completion theorem. It does NOT assert
that arbitrary HJ histories supply two ordinary side maps
compatible over a common generated Q, and is NOT the full
closed U-size j-to-j+1 increment.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Any weak structure fully embedded in a finite maximal-U-rank
source has maximal intrinsic U-rank itself, even if neither
structure is U-closed and the embedded range is not a closed
substructure of the source. -/
theorem Embedding.USize_eq_card_of_embedding_into_maximal
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    [Fintype U] [Fintype V]
    (hMax : USize rules B = Fintype.card V)
    (e : Embedding A B) :
    USize rules A = Fintype.card U := by
  have hAllB := all_subsets_relative_of_USize_eq_card rules B hMax
  have hAllA : ∀ S : Set U, IsUSubstructure rules A S := by
    intro S rule hrule t ht hRoot j
    have htB : B.rel rule.symbol (e ∘ t) :=
      (e.map_rel_iff rule.symbol t).mpr ht
    have hRootB : ∀ i : Fin rule.rootSize,
        (e ∘ t) (i.castLE rule.rootLE) ∈ e '' S := by
      intro i
      exact ⟨t (i.castLE rule.rootLE), hRoot i, rfl⟩
    obtain ⟨x, hx, heq⟩ :=
      hAllB (e '' S) rule hrule (e ∘ t) htB hRootB j
    have htEq : t j = x := (e.injective heq).symm
    exact htEq ▸ hx
  exact USize_eq_card_of_all_subsets_relative rules A hAllA

variable {H E F C W P : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E}
variable {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {D : RelStructure L W}
variable {Q : RelStructure L P}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}

/-- A maximal-rank exact weak free source can be completed from TWO
separate ORDINARY homomorphism-embeddings of its small sides into
one old closed control D, as long as the common root is compatible
with a single GENERATED U-closed Q∈K through two possibly distinct
Q embeddings into D.

Unlike the underlying two-side completion theorem, this result
derives relative U-closedness of both source side ranges and
protects the ordinary side maps; they are not extra premises.
This is the correct interface for native coordinate retractions
of transverse Hales--Jewett copy families.
-/
theorem HasClosedUKCompletion.of_maximal_weak_two_ordinary_side_maps
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    [Fintype C] [Fintype E] [Fintype F]
    [Finite W] [Finite P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hDClosed : IsUClosed rules D)
    (hQK : K Q) (hQClosed : IsUClosed rules Q)
    (q : H → P)
    (hQGenerated : IsUGenerating rules Q (Set.range q))
    (pL : E → W) (pR : F → W)
    (hpL : Left.IsHomomorphismEmbedding D pL)
    (hpR : Right.IsHomomorphismEmbedding D pR)
    (aL aR : Embedding Q D)
    (hRootL : ∀ r : H, pL (sL r) = aL (q r))
    (hRootR : ∀ r : H, pR (sR r) = aR (q r))
    (j : ℕ)
    (hCardL : Fintype.card E ≤ j)
    (hCardR : Fintype.card F ≤ j)
    (hRank : ∀ (T : Set W) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules Whole := by
  have hAll :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
  have hRelL : IsUSubstructure rules Whole (Set.range iL) :=
    hAll (Set.range iL)
  have hRelR : IsUSubstructure rules Whole (Set.range iR) :=
    hAll (Set.range iR)
  have hMaxL : USize rules Left = Fintype.card E :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iL
  have hMaxR : USize rules Right = Fintype.card F :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iR
  have hpL' : IsClosedUHomomorphismEmbedding rules Left D pL :=
    hpL.toClosedMap_of_max_USize hMaxL
  have hpR' : IsClosedUHomomorphismEmbedding rules Right D pR :=
    hpR.toClosedMap_of_max_USize hMaxR
  exact HasClosedUKCompletion.of_two_small_side_projections
    rules hK hKIrr hSrc hRelL hRelR
    hDClosed hQK hQClosed q hQGenerated
    pL pR hpL' hpR' aL aR hRootL hRootR
    j hCardL hCardR hRank

end StructuralRamsey.RelStructure
