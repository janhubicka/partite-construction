import PartiteConstruction.Functional.MixedOverlapExactness
import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-! # Strict tree extensions and common-subtree amalgamation

A reducible functional overlap cannot in general be forced into one
irreducible target copy.  The correct replacement is to first complete the
overlap to a tree and require both side witnesses to extend that same root
tree.

A TreeExtension records a target obtained from an existing structure by
successively attaching fresh copies of Base using the strict tree-amalgam
root condition.  Such extensions are functorial: an extension can be replayed
on top of any embedded copy of its start.  Consequently two extensions of the
same start admit a common further extension in which their start embeddings
agree pointwise.

This is the strict-tree analogue of gluing ordinary trees along a common
subtree.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {VB VS : Type v}

/-- A finite sequence of strict Base-copy attachments starting from Start. -/
inductive TreeExtension
    (Base : Structure L VB) (Start : Structure L VS) :
    (W : Type v) -> Structure L W -> Type (max u v)
  | refl :
      TreeExtension Base Start VS Start
  | attach
      {W H : Type v}
      {T : Structure L W} {Root : Structure L H}
      (prev : TreeExtension Base Start W T)
      (fT : Embedding Root T) (fBase : Embedding Root Base)
      (hcT : fT.ContainedInIrreducible)
      (hcBase : fBase.ContainedInIrreducible) :
      TreeExtension Base Start
        (FreeAmalgam.Vertex Root T Base fT fBase)
        (FreeAmalgam.amalgam Root T Base fT fBase)

namespace TreeExtension

variable {Base : Structure L VB} {Start : Structure L VS}

/-- The canonical copy of the starting structure inside an extension. -/
noncomputable def startEmbedding
    {W : Type v} {T : Structure L W}
    (h : TreeExtension Base Start W T) :
    Embedding Start T := by
  induction h with
  | refl =>
      exact Embedding.id Start
  | @attach W H T Root prev fT fBase hcT hcBase ih =>
      exact
        (FreeAmalgam.leftEmbedding Root T Base fT fBase).comp ih

/-- Extending an already strict Base-tree preserves strict tree-amalgamhood. -/
theorem toTree
    {W : Type v} {T : Structure L W}
    (h : TreeExtension Base Start W T)
    (hStart : TreeAmalgam Base VS Start) :
    TreeAmalgam Base W T := by
  induction h with
  | refl =>
      exact hStart
  | @attach W H T Root prev fT fBase hcT hcBase ih =>
      let l := FreeAmalgam.leftEmbedding Root T Base fT fBase
      let r := FreeAmalgam.rightEmbedding Root T Base fT fBase
      exact TreeAmalgam.glue
        ih
        (TreeAmalgam.copy (Embedding.id Base) (by
          intro b
          exact ⟨b, rfl⟩))
        fT fBase hcT hcBase l r
        (FreeAmalgam.isFreeAmalgam Root T Base fT fBase)

/-- Replay an extension on top of an arbitrary embedded copy of its start.

The result is an extension of the new ambient target together with an
embedding of the old extension target into the replayed target.  The two
copies of Start agree pointwise. -/
theorem replay
    {W : Type v} {T : Structure L W}
    (h : TreeExtension Base Start W T)
    {M : Type v} {Mstr : Structure L M}
    (e0 : Embedding Start Mstr) :
    ∃ (Z : Type v) (Target : Structure L Z)
      (hExt : TreeExtension Base Mstr Z Target)
      (e : Embedding T Target),
        ∀ x : VS,
          e (h.startEmbedding x) =
            hExt.startEmbedding (e0 x) := by
  classical
  induction h with
  | refl =>
      refine ⟨M, Mstr, TreeExtension.refl, e0, ?_⟩
      intro x
      rfl
  | @attach W H T Root prev fT fBase hcT hcBase ih =>
      obtain ⟨Y, Mid, hMid, ePrev, hStart⟩ := ih
      let rMid : Embedding Root Mid := ePrev.comp fT
      have hcMid : rMid.ContainedInIrreducible :=
        hcT.postcomp ePrev
      let Target :=
        FreeAmalgam.amalgam Root Mid Base rMid fBase
      let lT :=
        FreeAmalgam.leftEmbedding Root T Base fT fBase
      let rT :=
        FreeAmalgam.rightEmbedding Root T Base fT fBase
      let lM :=
        FreeAmalgam.leftEmbedding Root Mid Base rMid fBase
      let rM :=
        FreeAmalgam.rightEmbedding Root Mid Base rMid fBase
      have hSrc : IsFreeAmalgam fT fBase lT rT :=
        FreeAmalgam.isFreeAmalgam Root T Base fT fBase
      have hTgt : IsFreeAmalgam rMid fBase lM rM :=
        FreeAmalgam.isFreeAmalgam Root Mid Base rMid fBase
      have hrootL :
          IsFreeAmalgam.RootIsolated fT rMid id ePrev := by
        intro a d had
        refine ⟨d, ?_, rfl⟩
        apply ePrev.injective
        exact had
      have hrootR :
          IsFreeAmalgam.RootIsolated fBase fBase id
            (Embedding.id Base) := by
        intro b d hbd
        refine ⟨d, ?_, rfl⟩
        exact hbd
      let eNew : Embedding
          (FreeAmalgam.Vertex Root T Base fT fBase)
          (FreeAmalgam.Vertex Root Mid Base rMid fBase) :=
        IsFreeAmalgam.functionalLiftEmbedding
          hSrc hTgt id Function.injective_id
          ePrev (Embedding.id Base)
          (fun _ => rfl) (fun _ => rfl)
          hrootL hrootR
      let hFinal : TreeExtension Base Mstr
          (FreeAmalgam.Vertex Root Mid Base rMid fBase) Target :=
        TreeExtension.attach hMid rMid fBase hcMid hcBase
      refine ⟨_, Target, hFinal, eNew, ?_⟩
      intro x
      change
        eNew (lT (prev.startEmbedding x)) =
          lM
            ((TreeExtension.startEmbedding
              (Base := Base) (Start := Mstr) hMid) (e0 x))
      calc
        eNew (lT (prev.startEmbedding x)) =
            lM (ePrev (prev.startEmbedding x)) :=
          IsFreeAmalgam.functionalLiftMap_left
            hSrc hTgt id ePrev (Embedding.id Base)
            (fun _ => rfl) (fun _ => rfl)
            (prev.startEmbedding x)
        _ =
            lM
              ((TreeExtension.startEmbedding
                (Base := Base) (Start := Mstr) hMid) (e0 x)) :=
          congrArg lM (hStart x)

/-- Two extensions of the same start embed compatibly into one common
extension. -/
theorem merge
    {WL WR : Type v}
    {TL : Structure L WL} {TR : Structure L WR}
    (hL : TreeExtension Base Start WL TL)
    (hR : TreeExtension Base Start WR TR) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeExtension Base TL Z Target ∧
      ∃ eL : Embedding TL Target,
        ∃ eR : Embedding TR Target,
          ∀ x : VS,
            eL (hL.startEmbedding x) =
              eR (hR.startEmbedding x) := by
  classical
  obtain ⟨Z, Target, hExt, eR, hcompat⟩ :=
    hR.replay hL.startEmbedding
  let eL : Embedding TL Target :=
    hExt.startEmbedding
  refine ⟨Z, Target, hExt, eL, eR, ?_⟩
  intro x
  exact (hcompat x).symm

/-- If the common start is already a Base-tree, the merged target is too. -/
theorem merge_tree
    {WL WR : Type v}
    {TL : Structure L WL} {TR : Structure L WR}
    (hStart : TreeAmalgam Base VS Start)
    (hL : TreeExtension Base Start WL TL)
    (hR : TreeExtension Base Start WR TR) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ eL : Embedding TL Target,
        ∃ eR : Embedding TR Target,
          ∀ x : VS,
            eL (hL.startEmbedding x) =
              eR (hR.startEmbedding x) := by
  obtain ⟨Z, Target, hExt, eL, eR, hcompat⟩ :=
    hL.merge hR
  exact ⟨Z, Target, hExt.toTree (hL.toTree hStart),
    eL, eR, hcompat⟩

end TreeExtension
end StructuralRamsey.Structure
