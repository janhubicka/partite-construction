import PartiteConstruction.Functional.MixedOverlapExactness
import PartiteConstruction.Functional.FreeAmalgamReassociate
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
    (W : Type v) -> Structure L W -> Type (max (u + 1) (v + 1))
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
  | attachTree
      {W H X : Type v}
      {T : Structure L W} {Root : Structure L H}
      {Branch : Structure L X}
      (prev : TreeExtension Base Start W T)
      (hBranch : TreeAmalgam Base X Branch)
      (fT : Embedding Root T) (fBranch : Embedding Root Branch)
      (hcT : fT.ContainedInIrreducible)
      (hcBranch : fBranch.ContainedInIrreducible) :
      TreeExtension Base Start
        (FreeAmalgam.Vertex Root T Branch fT fBranch)
        (FreeAmalgam.amalgam Root T Branch fT fBranch)

namespace TreeExtension

variable {Base : Structure L VB} {Start : Structure L VS}


/-- Concatenate two strict tree extensions. -/
noncomputable def trans
    {W X : Type v}
    {T : Structure L W} {R : Structure L X}
    (h₁ : TreeExtension Base Start W T)
    (h₂ : TreeExtension Base T X R) :
    TreeExtension Base Start X R := by
  induction h₂ with
  | refl =>
      exact h₁
  | @attach W' H T' Root prev fT fBase hcT hcBase ih =>
      exact TreeExtension.attach ih fT fBase hcT hcBase
  | @attachTree W' H Y T' Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      exact TreeExtension.attachTree ih hBranch
        fT fBranch hcT hcBranch

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
  | @attachTree W H X T Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      exact
        (FreeAmalgam.leftEmbedding Root T Branch fT fBranch).comp ih


/-- The canonical start embedding of a concatenated extension is the
composition of the two canonical start embeddings. -/
theorem startEmbedding_trans
    {W X : Type v}
    {T : Structure L W} {R : Structure L X}
    (h₁ : TreeExtension Base Start W T)
    (h₂ : TreeExtension Base T X R)
    (x : VS) :
    (h₁.trans h₂).startEmbedding x =
      h₂.startEmbedding (h₁.startEmbedding x) := by
  induction h₂ with
  | refl =>
      rfl
  | @attach W' H T' Root prev fT fBase hcT hcBase ih =>
      change
        (FreeAmalgam.leftEmbedding Root T' Base fT fBase)
            ((h₁.trans prev).startEmbedding x) =
          (FreeAmalgam.leftEmbedding Root T' Base fT fBase)
            (prev.startEmbedding (h₁.startEmbedding x))
      exact congrArg
        (FreeAmalgam.leftEmbedding Root T' Base fT fBase)
        ih
  | @attachTree W' H Y T' Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      change
        (FreeAmalgam.leftEmbedding Root T' Branch fT fBranch)
            ((h₁.trans prev).startEmbedding x) =
          (FreeAmalgam.leftEmbedding Root T' Branch fT fBranch)
            (prev.startEmbedding (h₁.startEmbedding x))
      exact congrArg
        (FreeAmalgam.leftEmbedding Root T' Branch fT fBranch)
        ih

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
  | @attachTree W H X T Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      let l := FreeAmalgam.leftEmbedding Root T Branch fT fBranch
      let r := FreeAmalgam.rightEmbedding Root T Branch fT fBranch
      exact TreeAmalgam.glue
        ih hBranch fT fBranch hcT hcBranch l r
        (FreeAmalgam.isFreeAmalgam Root T Branch fT fBranch)

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
          (FreeAmalgam.amalgam Root T Base fT fBase)
          (FreeAmalgam.amalgam Root Mid Base rMid fBase) :=
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
  | @attachTree W H X T Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      obtain ⟨Y, Mid, hMid, ePrev, hStart⟩ := ih
      let rMid : Embedding Root Mid := ePrev.comp fT
      have hcMid : rMid.ContainedInIrreducible :=
        hcT.postcomp ePrev
      let Target :=
        FreeAmalgam.amalgam Root Mid Branch rMid fBranch
      let lT :=
        FreeAmalgam.leftEmbedding Root T Branch fT fBranch
      let rT :=
        FreeAmalgam.rightEmbedding Root T Branch fT fBranch
      let lM :=
        FreeAmalgam.leftEmbedding Root Mid Branch rMid fBranch
      let rM :=
        FreeAmalgam.rightEmbedding Root Mid Branch rMid fBranch
      have hSrc : IsFreeAmalgam fT fBranch lT rT :=
        FreeAmalgam.isFreeAmalgam Root T Branch fT fBranch
      have hTgt : IsFreeAmalgam rMid fBranch lM rM :=
        FreeAmalgam.isFreeAmalgam Root Mid Branch rMid fBranch
      have hrootL :
          IsFreeAmalgam.RootIsolated fT rMid id ePrev := by
        intro a d had
        refine ⟨d, ?_, rfl⟩
        apply ePrev.injective
        exact had
      have hrootR :
          IsFreeAmalgam.RootIsolated fBranch fBranch id
            (Embedding.id Branch) := by
        intro b d hbd
        refine ⟨d, ?_, rfl⟩
        exact hbd
      let eNew : Embedding
          (FreeAmalgam.amalgam Root T Branch fT fBranch)
          (FreeAmalgam.amalgam Root Mid Branch rMid fBranch) :=
        IsFreeAmalgam.functionalLiftEmbedding
          hSrc hTgt id Function.injective_id
          ePrev (Embedding.id Branch)
          (fun _ => rfl) (fun _ => rfl)
          hrootL hrootR
      let hFinal : TreeExtension Base Mstr
          (FreeAmalgam.Vertex Root Mid Branch rMid fBranch) Target :=
        TreeExtension.attachTree hMid hBranch
          rMid fBranch hcMid hcBranch
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
            hSrc hTgt id ePrev (Embedding.id Branch)
            (fun _ => rfl) (fun _ => rfl)
            (prev.startEmbedding x)
        _ =
            lM
              ((TreeExtension.startEmbedding
                (Base := Base) (Start := Mstr) hMid) (e0 x)) :=
          congrArg lM (hStart x)


/-- Replay an extension over a new ambient target, retaining the full
free-amalgam certificate over the common start.

This is the strengthened form used for reducible mixed roots: after replay,
the new ambient target and the old extension meet *exactly* in Start, not just
pointwise on its image. -/
theorem replayFree
    {W : Type v} {T : Structure L W}
    (h : TreeExtension Base Start W T)
    {M : Type v} {Mstr : Structure L M}
    (e0 : Embedding Start Mstr) :
    ∃ (Z : Type v) (Target : Structure L Z)
      (hExt : TreeExtension Base Mstr Z Target)
      (e : Embedding T Target),
        IsFreeAmalgam e0 h.startEmbedding hExt.startEmbedding e ∧
        ∀ x : VS,
          e (h.startEmbedding x) =
            hExt.startEmbedding (e0 x) := by
  classical
  induction h with
  | refl =>
      refine ⟨M, Mstr, TreeExtension.refl, e0, ?_, ?_⟩
      · exact IsFreeAmalgam.right_identity e0
      · intro x
        rfl
  | @attach W H T Root prev fT fBase hcT hcBase ih =>
      obtain ⟨Y, Mid, hMid, ePrev, hPrevFree, hStart⟩ := ih
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
        exact ⟨d, hbd, rfl⟩
      let eNew : Embedding
          (FreeAmalgam.amalgam Root T Base fT fBase)
          (FreeAmalgam.amalgam Root Mid Base rMid fBase) :=
        IsFreeAmalgam.functionalLiftEmbedding
          hSrc hTgt id Function.injective_id
          ePrev (Embedding.id Base)
          (fun _ => rfl) (fun _ => rfl)
          hrootL hrootR
      let hFinal : TreeExtension Base Mstr
          (FreeAmalgam.Vertex Root Mid Base rMid fBase) Target :=
        TreeExtension.attach hMid rMid fBase hcMid hcBase
      have heT : ∀ t : W, eNew (lT t) = lM (ePrev t) := by
        intro t
        exact IsFreeAmalgam.functionalLiftMap_left
          hSrc hTgt id ePrev (Embedding.id Base)
          (fun _ => rfl) (fun _ => rfl) t
      have heB : ∀ b : VB, eNew (rT b) = rM b := by
        intro b
        exact IsFreeAmalgam.functionalLiftMap_right
          hSrc hTgt id ePrev (Embedding.id Base)
          (fun _ => rfl) (fun _ => rfl) b
      have hFree :
          IsFreeAmalgam
            e0 (lT.comp prev.startEmbedding)
            (lM.comp hMid.startEmbedding) eNew :=
        IsFreeAmalgam.reassociate_right
          hPrevFree hSrc hTgt eNew heT heB
      refine ⟨_, Target, hFinal, eNew, ?_, ?_⟩
      · change
          IsFreeAmalgam
            e0 (lT.comp prev.startEmbedding)
            (lM.comp hMid.startEmbedding) eNew
        exact hFree
      · intro x
        change
          eNew (lT (prev.startEmbedding x)) =
            lM (hMid.startEmbedding (e0 x))
        calc
          eNew (lT (prev.startEmbedding x)) =
              lM (ePrev (prev.startEmbedding x)) :=
            heT (prev.startEmbedding x)
          _ = lM (hMid.startEmbedding (e0 x)) :=
            congrArg lM (hStart x)
  | @attachTree W H X T Root Branch prev hBranch
      fT fBranch hcT hcBranch ih =>
      obtain ⟨Y, Mid, hMid, ePrev, hPrevFree, hStart⟩ := ih
      let rMid : Embedding Root Mid := ePrev.comp fT
      have hcMid : rMid.ContainedInIrreducible :=
        hcT.postcomp ePrev
      let Target :=
        FreeAmalgam.amalgam Root Mid Branch rMid fBranch
      let lT :=
        FreeAmalgam.leftEmbedding Root T Branch fT fBranch
      let rT :=
        FreeAmalgam.rightEmbedding Root T Branch fT fBranch
      let lM :=
        FreeAmalgam.leftEmbedding Root Mid Branch rMid fBranch
      let rM :=
        FreeAmalgam.rightEmbedding Root Mid Branch rMid fBranch
      have hSrc : IsFreeAmalgam fT fBranch lT rT :=
        FreeAmalgam.isFreeAmalgam Root T Branch fT fBranch
      have hTgt : IsFreeAmalgam rMid fBranch lM rM :=
        FreeAmalgam.isFreeAmalgam Root Mid Branch rMid fBranch
      have hrootL :
          IsFreeAmalgam.RootIsolated fT rMid id ePrev := by
        intro a d had
        refine ⟨d, ?_, rfl⟩
        apply ePrev.injective
        exact had
      have hrootR :
          IsFreeAmalgam.RootIsolated fBranch fBranch id
            (Embedding.id Branch) := by
        intro b d hbd
        exact ⟨d, hbd, rfl⟩
      let eNew : Embedding
          (FreeAmalgam.amalgam Root T Branch fT fBranch)
          (FreeAmalgam.amalgam Root Mid Branch rMid fBranch) :=
        IsFreeAmalgam.functionalLiftEmbedding
          hSrc hTgt id Function.injective_id
          ePrev (Embedding.id Branch)
          (fun _ => rfl) (fun _ => rfl)
          hrootL hrootR
      let hFinal : TreeExtension Base Mstr
          (FreeAmalgam.Vertex Root Mid Branch rMid fBranch) Target :=
        TreeExtension.attachTree hMid hBranch
          rMid fBranch hcMid hcBranch
      have heT : ∀ t : W, eNew (lT t) = lM (ePrev t) := by
        intro t
        exact IsFreeAmalgam.functionalLiftMap_left
          hSrc hTgt id ePrev (Embedding.id Branch)
          (fun _ => rfl) (fun _ => rfl) t
      have heBranch : ∀ b : X, eNew (rT b) = rM b := by
        intro b
        exact IsFreeAmalgam.functionalLiftMap_right
          hSrc hTgt id ePrev (Embedding.id Branch)
          (fun _ => rfl) (fun _ => rfl) b
      have hFree :
          IsFreeAmalgam
            e0 (lT.comp prev.startEmbedding)
            (lM.comp hMid.startEmbedding) eNew :=
        IsFreeAmalgam.reassociate_right
          hPrevFree hSrc hTgt eNew heT heBranch
      refine ⟨_, Target, hFinal, eNew, ?_, ?_⟩
      · change
          IsFreeAmalgam
            e0 (lT.comp prev.startEmbedding)
            (lM.comp hMid.startEmbedding) eNew
        exact hFree
      · intro x
        change
          eNew (lT (prev.startEmbedding x)) =
            lM (hMid.startEmbedding (e0 x))
        calc
          eNew (lT (prev.startEmbedding x)) =
              lM (ePrev (prev.startEmbedding x)) :=
            heT (prev.startEmbedding x)
          _ = lM (hMid.startEmbedding (e0 x)) :=
            congrArg lM (hStart x)

/-- Two strict extensions of the same start have a common strict target in
which they form a genuine free amalgam over that start. -/
theorem mergeFree_tree
    {WL WR : Type v}
    {TL : Structure L WL} {TR : Structure L WR}
    (hStart : TreeAmalgam Base VS Start)
    (hL : TreeExtension Base Start WL TL)
    (hR : TreeExtension Base Start WR TR) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ eL : Embedding TL Target,
        ∃ eR : Embedding TR Target,
          IsFreeAmalgam
            hL.startEmbedding hR.startEmbedding eL eR := by
  obtain ⟨Z, Target, hExt, eR, hFree, _⟩ :=
    hR.replayFree hL.startEmbedding
  let eL : Embedding TL Target := hExt.startEmbedding
  have hTL : TreeAmalgam Base WL TL :=
    hL.toTree hStart
  have hTarget : TreeAmalgam Base Z Target :=
    hExt.toTree hTL
  exact ⟨Z, Target, hTarget, eL, eR, hFree⟩

/-- A strict tree can be rerooted at any chosen embedded copy of an
irreducible finite base, after embedding it into a further strict extension.

The further target is an extension of the base itself, and the chosen copy is
identified with the canonical starting copy. -/
theorem embedIntoRootedExtension
    [Finite VB]
    (hBase : Base.Irreducible)
    {W : Type v} {T : Structure L W}
    (hT : TreeAmalgam Base W T) :
    ∀ j : Embedding Base T,
      ∃ (Z : Type v) (Target : Structure L Z)
        (hExt : TreeExtension Base Base Z Target)
        (e : Embedding T Target),
        ∀ b : VB, e (j b) = hExt.startEmbedding b := by
  classical
  induction hT with
  | @copy W T e0 hsurj =>
      intro j
      let eqv : VB ≃ W :=
        Equiv.ofBijective e0 ⟨e0.injective, hsurj⟩
      have hjSurj : Function.Surjective j :=
        (Finite.injective_iff_surjective_of_equiv eqv).mp j.injective
      let hRange :
          ∀ y : W, ∃ b : VB, (Embedding.id T) y = j b := by
        intro y
        obtain ⟨b, hb⟩ := hjSurj y
        exact ⟨b, hb.symm⟩
      let jInv : Embedding T Base :=
        (Embedding.id T).factorThroughClosedRange j hRange
      refine ⟨VB, Base, TreeExtension.refl, jInv, ?_⟩
      intro b
      change jInv (j b) = b
      apply j.injective
      have hs := Classical.choose_spec (hRange (j b))
      exact hs.symm
  | @glue W₁ W₂ H W T₁ T₂ Root T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      intro j
      rcases hfree.irreducible_side hBase j with hleft | hright
      · let j₁ : Embedding Base T₁ :=
          j.factorThroughClosedRange i₁ hleft
        have hj₁ (b : VB) : j b = i₁ (j₁ b) :=
          Classical.choose_spec (hleft b)
        obtain ⟨Z₁, R₁, hExt₁, e₁, he₁⟩ := ih₁ j₁
        let r₁ : Embedding Root R₁ := e₁.comp f₁
        have hcr₁ : r₁.ContainedInIrreducible :=
          hc₁.postcomp e₁
        let Target := FreeAmalgam.amalgam Root R₁ T₂ r₁ f₂
        let lT := FreeAmalgam.leftEmbedding Root T₁ T₂ f₁ f₂
        let rT := FreeAmalgam.rightEmbedding Root T₁ T₂ f₁ f₂
        let lR := FreeAmalgam.leftEmbedding Root R₁ T₂ r₁ f₂
        let rR := FreeAmalgam.rightEmbedding Root R₁ T₂ r₁ f₂
        have hTgt : IsFreeAmalgam r₁ f₂ lR rR :=
          FreeAmalgam.isFreeAmalgam Root R₁ T₂ r₁ f₂
        have hrootL : IsFreeAmalgam.RootIsolated f₁ r₁ id e₁ := by
          intro x d hxd
          refine ⟨d, ?_, rfl⟩
          apply e₁.injective
          exact hxd
        have hrootR :
            IsFreeAmalgam.RootIsolated f₂ f₂ id
              (Embedding.id T₂) := by
          intro x d hxd
          exact ⟨d, hxd, rfl⟩
        let eWhole : Embedding T Target :=
          IsFreeAmalgam.functionalLiftEmbedding
            hfree hTgt id Function.injective_id
            e₁ (Embedding.id T₂)
            (fun _ => rfl) (fun _ => rfl)
            hrootL hrootR
        let hFinal : TreeExtension Base Base
            (FreeAmalgam.Vertex Root R₁ T₂ r₁ f₂) Target :=
          TreeExtension.attachTree hExt₁ h₂
            r₁ f₂ hcr₁ hc₂
        refine ⟨_, Target, hFinal, eWhole, ?_⟩
        intro b
        change eWhole (j b) = lR (hExt₁.startEmbedding b)
        calc
          eWhole (j b) = eWhole (i₁ (j₁ b)) :=
            congrArg eWhole (hj₁ b)
          _ = lR (e₁ (j₁ b)) :=
            IsFreeAmalgam.functionalLiftMap_left
              hfree hTgt id e₁ (Embedding.id T₂)
              (fun _ => rfl) (fun _ => rfl) (j₁ b)
          _ = lR (hExt₁.startEmbedding b) :=
            congrArg lR (he₁ b)
      · let j₂ : Embedding Base T₂ :=
          j.factorThroughClosedRange i₂ hright
        have hj₂ (b : VB) : j b = i₂ (j₂ b) :=
          Classical.choose_spec (hright b)
        obtain ⟨Z₂, R₂, hExt₂, e₂, he₂⟩ := ih₂ j₂
        let r₂ : Embedding Root R₂ := e₂.comp f₂
        have hcr₂ : r₂.ContainedInIrreducible :=
          hc₂.postcomp e₂
        let Target := FreeAmalgam.amalgam Root R₂ T₁ r₂ f₁
        let lR := FreeAmalgam.leftEmbedding Root R₂ T₁ r₂ f₁
        let rR := FreeAmalgam.rightEmbedding Root R₂ T₁ r₂ f₁
        have hSrc : IsFreeAmalgam f₂ f₁ i₂ i₁ :=
          hfree.swap
        have hTgt : IsFreeAmalgam r₂ f₁ lR rR :=
          FreeAmalgam.isFreeAmalgam Root R₂ T₁ r₂ f₁
        have hrootL : IsFreeAmalgam.RootIsolated f₂ r₂ id e₂ := by
          intro x d hxd
          refine ⟨d, ?_, rfl⟩
          apply e₂.injective
          exact hxd
        have hrootR :
            IsFreeAmalgam.RootIsolated f₁ f₁ id
              (Embedding.id T₁) := by
          intro x d hxd
          exact ⟨d, hxd, rfl⟩
        let eWhole : Embedding T Target :=
          IsFreeAmalgam.functionalLiftEmbedding
            hSrc hTgt id Function.injective_id
            e₂ (Embedding.id T₁)
            (fun _ => rfl) (fun _ => rfl)
            hrootL hrootR
        let hFinal : TreeExtension Base Base
            (FreeAmalgam.Vertex Root R₂ T₁ r₂ f₁) Target :=
          TreeExtension.attachTree hExt₂ h₁
            r₂ f₁ hcr₂ hc₁
        refine ⟨_, Target, hFinal, eWhole, ?_⟩
        intro b
        change eWhole (j b) = lR (hExt₂.startEmbedding b)
        calc
          eWhole (j b) = eWhole (i₂ (j₂ b)) :=
            congrArg eWhole (hj₂ b)
          _ = lR (e₂ (j₂ b)) :=
            IsFreeAmalgam.functionalLiftMap_left
              hSrc hTgt id e₂ (Embedding.id T₁)
              (fun _ => rfl) (fun _ => rfl) (j₂ b)
          _ = lR (hExt₂.startEmbedding b) :=
            congrArg lR (he₂ b)

/-- Two extensions of the same start embed compatibly into one common
extension. -/
theorem merge
    {WL WR : Type v}
    {TL : Structure L WL} {TR : Structure L WR}
    (hL : TreeExtension Base Start WL TL)
    (hR : TreeExtension Base Start WR TR) :
    ∃ (Z : Type v) (Target : Structure L Z)
      (hExt : TreeExtension Base TL Z Target),
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
