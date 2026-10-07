import PartiteConstruction.Functional.TreeExtensionHistoryWitness

/-! # Relative functional histories through strict root-tree extensions

A reducible common boundary cannot always be represented by an embedded
A-copy.  The required recursive object is instead a full side witness
extending a fixed strict tree completion of the boundary.

This file establishes the operations required by that recursion.  Finite
histories concern the *outer projection*, so they survive a quotient of the
boundary whenever this projection factors through the quotient.  In
particular, free gluing preserves the original distinguished root and the
full extension certificate: the result can be passed to another induction
step, rather than merely yielding a final tree completion.
-/

namespace StructuralRamsey.Structure.HasTreeExtensionProjectedHistoryCompletion

universe u v

variable {L : Language.{u}}
variable {VB H E P G : Type v}
variable {Base : Structure L VB}
variable {Root : Structure L H}
variable {Side : Structure L E}
variable {Start : Structure L G}

/-- The source root itself is a relative completion provided the outer
projection factors through its chosen tree-completion map.  No injectivity
of that map is required. -/
theorem root_of_projectedFactor
    (q : H → G)
    (hq : Root.IsHomomorphismEmbedding Start q)
    (p : H → P) (pG : G → P)
    (hproj : ∀ x, p x = pG (q x))
    (history : List (Set P)) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start)
      (Embedding.id Root) q p history := by
  let hExt : TreeExtension Base Start G Start := TreeExtension.refl
  refine ⟨G, Start, hExt, q, hq, ?_, ?_, ?_⟩
  · intro d
    rfl
  · intro x a hxa
    exact ⟨x, rfl, hxa⟩
  · intro K _ x y hxy
    rw [hproj x, hproj y, hxy]

/-- Restrictions to a smaller collection of projected history requests. -/
theorem mono_history
    {s : Embedding Root Side} {q : H → G} {p : E → P}
    {large small : List (Set P)}
    (h : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p large)
    (hsub : ∀ K ∈ small, K ∈ large) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p small := by
  obtain ⟨Z, T, hExt, f, hf, hc, hi, hh⟩ := h
  exact ⟨Z, T, hExt, f, hf, hc, hi,
    fun K hK x y hxy => hh K (hsub K hK) x y hxy⟩

/-- Pull back a full side witness along a full source embedding, retaining
the exact root-isolation certificate and the pulled-back outer projection. -/
theorem pullback_embedding
    {E₁ : Type v} {Side₁ : Structure L E₁}
    {s : Embedding Root Side} {q : H → G}
    (j : Embedding Side₁ Side)
    (s₁ : Embedding Root Side₁)
    (hcomm : ∀ d, j (s₁ d) = s d)
    (p : E → P) (history : List (Set P))
    (h : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p history) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s₁ q (p ∘ j) history := by
  obtain ⟨Z, T, hExt, f, hf, hc, hi, hh⟩ := h
  let f₁ : E₁ → Z := f ∘ j
  have hf₁ : Side₁.IsHomomorphismEmbedding T f₁ :=
    hf.comp j.isHomomorphismEmbedding
  have hc₁ : ∀ d, f₁ (s₁ d) = hExt.startEmbedding (q d) := by
    intro d
    change f (j (s₁ d)) = hExt.startEmbedding (q d)
    rw [hcomm d]
    exact hc d
  have hi₁ : IsFreeAmalgam.RootIsolated
      s₁ hExt.startEmbedding q f₁ := by
    intro x a hxa
    obtain ⟨d, hxd, hda⟩ := hi (j x) a hxa
    refine ⟨d, ?_, hda⟩
    apply j.injective
    calc
      j x = s d := hxd
      _ = j (s₁ d) := (hcomm d).symm
  have hh₁ :
      ∀ K ∈ history, ∀ x y : E₁,
        f₁ x = f₁ y → ((p ∘ j) x ∈ K ↔ (p ∘ j) y ∈ K) := by
    intro K hK x y hxy
    exact hh K hK (j x) (j y) hxy
  exact ⟨Z, T, hExt, f₁, hf₁, hc₁, hi₁, hh₁⟩

/-- Replay a relative completion on top of a further strict extension of
its start.  The target embedding is injective and so transports all
projected-history implications unchanged. -/
theorem rebase
    {s : Embedding Root Side}
    (q : H → G) (p : E → P) (history : List (Set P))
    (h : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) s q p history)
    {G₂ : Type v} {Start₂ : Structure L G₂}
    (hMore : TreeExtension Base Start G₂ Start₂) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start₂) s
      (hMore.startEmbedding ∘ q) p history := by
  classical
  obtain ⟨Z, T, hExt, f, hf, hc, hi, hh⟩ := h
  obtain ⟨Z₂, T₂, hExt₂, e, hFree, hStart⟩ :=
    hExt.replayFree hMore.startEmbedding
  let f₂ : E → Z₂ := e ∘ f
  have hf₂ : Side.IsHomomorphismEmbedding T₂ f₂ :=
    e.isHomomorphismEmbedding.comp hf
  have hc₂ :
      ∀ d, f₂ (s d) =
        hExt₂.startEmbedding ((hMore.startEmbedding ∘ q) d) := by
    intro d
    calc
      f₂ (s d) = e (f (s d)) := rfl
      _ = e (hExt.startEmbedding (q d)) := congrArg e (hc d)
      _ = hExt₂.startEmbedding (hMore.startEmbedding (q d)) :=
        hStart (q d)
  have hi₂ : IsFreeAmalgam.RootIsolated
      s hExt₂.startEmbedding (hMore.startEmbedding ∘ q) f₂ := by
    intro x a hxa
    obtain ⟨b, hab, hfb⟩ :=
      (hFree.overlap a (f x)).mp hxa.symm
    obtain ⟨d, hxd, hdb⟩ := hi x b hfb
    refine ⟨d, hxd, ?_⟩
    exact (congrArg hMore.startEmbedding hdb).trans hab.symm
  have hh₂ :
      ∀ K ∈ history, ∀ x y : E,
        f₂ x = f₂ y → (p x ∈ K ↔ p y ∈ K) := by
    intro K hK x y hxy
    exact hh K hK x y (e.injective hxy)
  exact ⟨Z₂, T₂, hExt₂, f₂, hf₂, hc₂, hi₂, hh₂⟩


/-- Free amalgamation of two source sides over the same distinguished root
preserves the *relative* strict-tree completion and finite projected histories.

This is the inductive form of the mixed gluing lemma: unlike a final
tree-completion conclusion, it can itself be glued into another side. -/
theorem glue_relative
    {F C : Type v} {Right : Structure L F} {Whole : Structure L C}
    {sL : Embedding Root Side} {sR : Embedding Root Right}
    {iL : Embedding Side Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (q : H → G)
    (pWhole : C → P) (pL : E → P) (pR : F → P)
    (pG : G → P)
    (hpL : ∀ x, pWhole (iL x) = pL x)
    (hpR : ∀ x, pWhole (iR x) = pR x)
    (hrootProjL : ∀ d, pL (sL d) = pG (q d))
    (hrootProjR : ∀ d, pR (sR d) = pG (q d))
    (history : List (Set P))
    (hL : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) sL q pL history)
    (hR : HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start) sR q pR history) :
    HasTreeExtensionProjectedHistoryCompletion
      (Base := Base) (Start := Start)
      (iL.comp sL) q pWhole history := by
  classical
  obtain ⟨ZL, TL, hExtL, fL, hfL, hcL, hiL, hhL⟩ := hL
  obtain ⟨ZR, TR, hExtR, fR, hfR, hcR, hiR, hhR⟩ := hR
  obtain ⟨Z, T, hExt, eL, eR, hTgt, hStartL, hStartR⟩ :=
    hExtL.mergeFree hExtR
  let f : C → Z :=
    IsFreeAmalgam.functionalLiftMap
      hSrc hTgt q fL fR hcL hcR
  have hf : Whole.IsHomomorphismEmbedding T f :=
    IsFreeAmalgam.functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcL hcR hfL hfR hiL hiR
  have hc : ∀ d, f ((iL.comp sL) d) = hExt.startEmbedding (q d) := by
    intro d
    calc
      f (iL (sL d)) = eL (fL (sL d)) :=
        IsFreeAmalgam.functionalLiftMap_left
          hSrc hTgt q fL fR hcL hcR (sL d)
      _ = eL (hExtL.startEmbedding (q d)) := congrArg eL (hcL d)
      _ = hExt.startEmbedding (q d) := hStartL (q d)
  have hi : IsFreeAmalgam.RootIsolated
      (iL.comp sL) hExt.startEmbedding q f := by
    intro x a hxa
    rcases hSrc.covers x with ⟨l, hxl⟩ | ⟨r, hxr⟩
    · have hside : fL l = hExtL.startEmbedding a := by
        apply eL.injective
        calc
          eL (fL l) = f (iL l) :=
            (IsFreeAmalgam.functionalLiftMap_left
              hSrc hTgt q fL fR hcL hcR l).symm
          _ = f x := congrArg f hxl.symm
          _ = hExt.startEmbedding a := hxa
          _ = eL (hExtL.startEmbedding a) := (hStartL a).symm
      obtain ⟨d, hld, hda⟩ := hiL l a hside
      refine ⟨d, ?_, hda⟩
      change x = iL (sL d)
      exact hxl.trans (congrArg iL hld)
    · have hside : fR r = hExtR.startEmbedding a := by
        apply eR.injective
        calc
          eR (fR r) = f (iR r) :=
            (IsFreeAmalgam.functionalLiftMap_right
              hSrc hTgt q fL fR hcL hcR r).symm
          _ = f x := congrArg f hxr.symm
          _ = hExt.startEmbedding a := hxa
          _ = eR (hExtR.startEmbedding a) := (hStartR a).symm
      obtain ⟨d, hrd, hda⟩ := hiR r a hside
      refine ⟨d, ?_, hda⟩
      change x = iL (sL d)
      calc
        x = iR r := hxr
        _ = iR (sR d) := congrArg iR hrd
        _ = iL (sL d) :=
          ((hSrc.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩).symm
  have hh :
      ∀ K ∈ history, ∀ x y : C,
        f x = f y → (pWhole x ∈ K ↔ pWhole y ∈ K) :=
    IsFreeAmalgam.functionalLiftMap_respectsProjectedSets
      hSrc hTgt q fL fR hcL hcR hiL hiR
      pWhole pL pR pG hpL hpR hrootProjL hrootProjR
      history hhL hhR
  exact ⟨Z, T, hExt, f, hf, hc, hi, hh⟩

end StructuralRamsey.Structure.HasTreeExtensionProjectedHistoryCompletion
