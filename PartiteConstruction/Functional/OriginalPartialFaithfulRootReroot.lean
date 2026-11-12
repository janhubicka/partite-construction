import PartiteConstruction.Functional.OriginalPartialFullSideRootAnchor
import PartiteConstruction.Functional.EHNGlobalDefectDecomposition

/-!
# Track D: reroot a genuinely partial side completion that is FULL only on its root

The previously verified rooted-extension theorem requires a FULL embedding
of the ENTIRE side into a strict Base-tree; another theorem only needs an
absolute EHN/2019-partial side completion, but assumes its root irreducible.

Neither restriction is essential to the target gluing construction. If an
original-partial side map is already a FULL embedding on its chosen common
root, and that root image sits in one irreducible Base constituent of the
strict target tree, we can attach a fresh prescribed Base over the root.
The side map may be highly noninjective away from the root; the root can
be reducible and multi-generated.

An additional theorem reduces full faithfulness of the root restriction
to precisely the three verified EHN defect conditions (injectivity,
relation reflection and source-defined function-domain reflection).

CRITICAL: this remains a CONDITIONAL target-root route. A canonical HJ
root label collision prevents these hypotheses on that label map. We
do not construct a side completion meeting the hypotheses, charge the
function-closed hull to the literal weak test, or establish the uniform
history-compatible maximal-mixed step in frozen Appendix A.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E VB Y : Type v}

/-- An original-2019 partial side completion can be rerooted over a
prescribed FULL embedding of its (possibly reducible) source separator
into Base whenever just the ROOT restriction of the chosen side map
is a full embedding into an irreducible constituent of its target tree.

The side map itself need NOT be a full embedding; this is strictly
weaker than the existing `of_full_tree_rooted` theorem.
-/
theorem HasOriginalPartialTreeExtensionCompletion.of_partial_side_full_root
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (T : Structure L Y)
    (hT : TreeAmalgam Base Y T)
    (p : E → Y)
    (hp : Side.IsOriginalPartialHomomorphismEmbedding T p)
    (rootT : Embedding Root T)
    (hRootT : rootT.ContainedInIrreducible)
    (hAgree : ∀ x : H, p (s x) = rootT x) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  let Target := FreeAmalgam.amalgam Root Base T q rootT
  have hQ : q.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro x
    exact ⟨q x, rfl⟩
  let ext : TreeExtension Base Base _ Target :=
    TreeExtension.attachTree TreeExtension.refl
      hT q rootT hQ hRootT
  let j : Embedding T Target :=
    FreeAmalgam.rightEmbedding Root Base T q rootT
  let pNew : E → FreeAmalgam.Vertex Root Base T q rootT :=
    j ∘ p
  have hpNew : IsOriginalPartialHomomorphismEmbedding
      Side Target pNew :=
    j.isEHNHomomorphismEmbedding.toOriginalPartial.comp hp
  have hFree : IsFreeAmalgam q rootT
      (FreeAmalgam.leftEmbedding Root Base T q rootT) j :=
    FreeAmalgam.isFreeAmalgam Root Base T q rootT
  refine ⟨_, Target, ext, pNew, hpNew, ?_⟩
  intro x
  change j (p (s x)) =
    (FreeAmalgam.leftEmbedding Root Base T q rootT) (q x)
  rw [hAgree x]
  exact ((hFree.overlap (q x) (rootT x)).mpr
    ⟨x, rfl, rfl⟩).symm

/-- Concrete defect-checking form. The restriction of the actual
original-partial side map to Root is FULL whenever (and precisely
because) it is injective, reflects old relations and reflects
nonempty function domains. The EHN condition supplies complete
fibre equality on all SOURCE-DEFINED inputs for free.

It is still necessary that this faithful root image land in ONE
irreducible Base-piece of the selected side target; this is NOT a
consequence of merely being a B-tree.
-/
theorem HasOriginalPartialTreeExtensionCompletion.of_partial_side_root_defects_absent
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (T : Structure L Y)
    (hT : TreeAmalgam Base Y T)
    (p : E → Y)
    (hp : Side.IsOriginalPartialHomomorphismEmbedding T p)
    (hInjective : Function.Injective (p ∘ s))
    (hRel :
      ∀ R xs, T.rel R ((p ∘ s) ∘ xs) → Root.rel R xs)
    (hDomain :
      ∀ F (xs : Fin (L.funcArity F) → H),
        (T.func F ((p ∘ s) ∘ xs)).Nonempty →
          (Root.func F xs).Nonempty)
    (piece : Embedding Base T)
    (hPiece : ∀ x : H, ∃ y : VB, p (s x) = piece y) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  have hpRoot : Root.IsEHNHomomorphismEmbedding T (p ∘ s) :=
    hp.toEHN.comp s.isEHNHomomorphismEmbedding
  obtain ⟨rootT, hRootEq⟩ :=
    hpRoot.fullEmbedding_iff_inj_reflect_rel_domain.mpr
      ⟨hInjective, hRel, hDomain⟩
  have hRootPiece : rootT.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, piece, ?_⟩
    intro x
    obtain ⟨y, hy⟩ := hPiece x
    exact ⟨y, (hRootEq x).trans hy⟩
  exact HasOriginalPartialTreeExtensionCompletion.of_partial_side_full_root
    Base hBase s q T hT p hp rootT hRootPiece
    (fun x => (hRootEq x).symm)

end StructuralRamsey.Structure
