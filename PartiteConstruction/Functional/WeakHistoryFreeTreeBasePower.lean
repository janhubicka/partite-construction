import PartiteConstruction.Functional.WeakHistoryFreeMixedRankStep
import PartiteConstruction.Functional.AmbientRelativeOneCopyCore
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Track D: arbitrary-rank strict native weak certificates for trees/powers

English proof committed FIRST at
docs/track-d-english-historyfree-tree-base-power-20261112.md.

Any genuine strict full-functional tree of irreducible Base-copies
has the history-FREE exact ambient-relative weak-tree certificate
at EVERY rank via its own identity embedding. Every genuine full
ambient A-copy lies inside a constituent Base-copy by the verified
irreducible localization theorem.

More generally an EHN map C→A followed by a FULL A↪Base
gives the same strict one-copy certificate on EVERY exact weak
source vertex set, with protection of all genuine ambient full
A-copy intersections. This covers the actual native HJ power core.
No projected histories, protected unoccupied marks, closed weak
subsets, or whole-fibre reflection on source-undefined inputs.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB W P : Type v}

/-- The original full structure C is itself a strict Base-tree,
so the identity restriction gives a strict functional weak-tree
witness on EVERY exact weak subset S. Genuine ambient A-copies
localize into irreducible Base constituents by the actual source
functional no-crossing irreducibility condition.

No projected-history assertion is made. -/
theorem of_strictTree_noHistory
    {A : Structure L UA} (hA : A.Irreducible)
    {Base : Structure L VB} (hBase : Base.Irreducible)
    {C : Structure L W}
    (hTree : TreeAmalgam Base W C)
    (p : W → P) (S : Set W) :
    SetAmbientRelativeWeakTreeWitness A Base C p S [] := by
  let f : S → W := fun x => x.1
  have hf : IsAmbientRelativeWeakHE C S C f :=
    (Embedding.id C).ambientRelativeWeakRestriction S
  have hCopies : SetAmbientACopyIntersections A C C S f := by
    intro e
    obtain ⟨j, hj⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy hA e
    have hc : e.ContainedInIrreducible := by
      refine ⟨VB, Base, hBase, j, ?_⟩
      intro a
      exact hj a
    refine ⟨e, hc, ?_⟩
    intro a ha
    rfl
  have hEmpty : SetRespectsProjectedHistory p S f [] := by
    intro H hH
    simp at hH
  exact ⟨W, C, hTree, f, hf, hCopies, hEmpty⟩

/-- A single genuine strict Base-copy suffices on ALL exact weak
sets of any EHN source C that maps into A, provided A fully embeds
into irreducible Base. The original EHN projection may COLLIDE
source vertices and need not reflect source-undefined domains.

All genuine ambient full A-copies in C obtain target FULL A marks
from the source EHN irreducibility clause and the fixed A↪Base. -/
theorem of_ehn_oneCopy_noHistory
    {A : Structure L UA} (hA : A.Irreducible)
    {Base : Structure L VB} (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    {C : Structure L W} {q : W → UA}
    (hq : C.IsEHNHomomorphismEmbedding A q)
    (p : W → P) (S : Set W) :
    SetAmbientRelativeWeakTreeWitness A Base C p S [] := by
  let f : S → VB := fun x => eAB (q x.1)
  have hf : IsAmbientRelativeWeakHE C S Base f :=
    hq.ambientRelativeWeak_to_embedding eAB S
  have hCopies : SetAmbientACopyIntersections A C Base S f := by
    intro e
    obtain ⟨eA, heA⟩ := hq.2 A hA e
    let eT : Embedding A Base := eAB.comp eA
    have hc : eT.ContainedInIrreducible := by
      refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
      intro a
      exact ⟨eT a, rfl⟩
    refine ⟨eT, hc, ?_⟩
    intro a ha
    change eAB (eA a) = eAB (q (e a))
    exact congrArg eAB (heA a)
  have hEmpty : SetRespectsProjectedHistory p S f [] := by
    intro H hH
    simp at hH
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  exact ⟨VB, Base, hTree, f, hf, hCopies, hEmpty⟩

/-- Any existing strict Base-tree satisfies ALL finite ranks of the
no-history exact functional weak invariant for any part map. -/
theorem AtMostNoHistory.of_strictTree
    {A : Structure L UA} (hA : A.Irreducible)
    {Base : Structure L VB} (hBase : Base.Irreducible)
    {C : Structure L W}
    (hTree : TreeAmalgam Base W C)
    (p : W → P) (n : ℕ) :
    AtMostNoHistory A Base C p n := by
  intro S _hS
  exact of_strictTree_noHistory hA hBase hTree p (↑S : Set W)

/-- An EHN source C projecting to a FULL A↪Base has
arbitrary-rank no-history strict FUNCTIONAL weak-tree certificates
for EVERY exact weak test (in particular the genuine HJ power core).
No EHN-domain reflection or cardinal bound is needed. -/
theorem AtMostNoHistory.of_ehn_oneCopy
    {A : Structure L UA} (hA : A.Irreducible)
    {Base : Structure L VB} (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    {C : Structure L W} {q : W → UA}
    (hq : C.IsEHNHomomorphismEmbedding A q)
    (p : W → P) (n : ℕ) :
    AtMostNoHistory A Base C p n := by
  intro S _hS
  exact of_ehn_oneCopy_noHistory hA hBase eAB hq p (↑S : Set W)

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
