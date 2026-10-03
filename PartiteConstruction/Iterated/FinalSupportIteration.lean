import PartiteConstruction.Iterated.FinalSupportStage

/-! # Iterating the uniform final-completion support stages

The support of every original irreducible root is a finite subset of Base.
There are therefore only finitely many support classes, independently of the
Ramsey witness.  One support class is handled by `attachSupport`.

This file iterates that theorem over all supports while carrying coverage of
all previously processed support classes.  The resulting initial local-tree
budget is an iterate of the fixed-support budget a number of times depending
only on Base.
-/
namespace StructuralRamsey.RelStructure.UniformFinal

open FinalSupport
open FinalCompletion

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB O Y : Type v}
variable (Control : RelStructure L UA)
variable (Base : RelStructure L VB)
variable (Orig : RelStructure L O)
variable (Q : RelStructure L Y)
variable (pOrig : O → Y)

/-- Iterate the one-support budget `k` times. -/
noncomputable def supportIterationBudget
    (UA VB : Type v) [Fintype UA] [Fintype VB] :
    ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n =>
      LocallyTreeLike.fixedSupportBudget UA VB
        (supportIterationBudget UA VB k n)

@[simp] theorem supportIterationBudget_zero
    [Fintype UA] [Fintype VB] (n : ℕ) :
    supportIterationBudget UA VB 0 n = n := rfl

@[simp] theorem supportIterationBudget_succ
    [Fintype UA] [Fintype VB] (k n : ℕ) :
    supportIterationBudget UA VB (k + 1) n =
      LocallyTreeLike.fixedSupportBudget UA VB
        (supportIterationBudget UA VB k n) := rfl

/-- Canonical list of all finite supports in Base. -/
noncomputable def allSupports [Fintype VB] : List (Finset VB) :=
  (Finset.univ.powerset).toList

/-- Uniform final-completion budget. -/
noncomputable def finalSupportBudget
    (UA VB : Type v) [Fintype UA] [Fintype VB] (n : ℕ) : ℕ :=
  supportIterationBudget UA VB (allSupports (VB := VB)).length n

/-- Coverage already obtained for every support in a finite list. -/
def CoversSupports
    [Fintype O]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    {m : ℕ}
    (S0 : Stage Control Base Orig Q pOrig m)
    (supports : List (Finset VB)) : Prop :=
  ∀ T, T ∈ supports →
    CoversSupport Control Base Orig Q pOrig hpOrig hProjected S0 T

/-- Coverage survives an arbitrary induced embedding of stages, provided the
new core is the composite of the old core with that embedding. -/
theorem CoversSupport.of_embedding
    [Fintype O]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    {m0 m1 : ℕ}
    {S0 : Stage Control Base Orig Q pOrig m0}
    {S1 : Stage Control Base Orig Q pOrig m1}
    (T : Finset VB)
    (e : Embedding S0.C S1.C)
    (hcore : S1.core = e.comp S0.core)
    (h : CoversSupport Control Base Orig Q pOrig
      hpOrig hProjected S0 T) :
    CoversSupport Control Base Orig Q pOrig
      hpOrig hProjected S1 T := by
  intro r
  obtain ⟨beta, hbeta⟩ := h r
  refine ⟨e.comp beta, ?_⟩
  intro z
  change S1.core z.1 =
    e (beta
      (FinalSupport.Root.toBase
        Orig Base Q pOrig hpOrig hProjected r.1 z))
  rw [hcore]
  exact congrArg e (hbeta z)

/-- Process a prescribed finite list of support classes. -/
theorem attachSupportList
    [Fintype UA] [Fintype VB] [Fintype O]
    (hControl : Control.Irreducible)
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    (supports : List (Finset VB))
    (n : ℕ)
    (S0 :
      Stage Control Base Orig Q pOrig
        (supportIterationBudget UA VB supports.length n)) :
    ∃ S1 : Stage Control Base Orig Q pOrig n,
      ∃ e : Embedding S0.C S1.C,
        (∀ x : S0.Vertex, S1.projection (e x) = S0.projection x) ∧
        S1.core = e.comp S0.core ∧
        CoversSupports Control Base Orig Q pOrig hpOrig hProjected
          S1 supports := by
  classical
  induction supports with
  | nil =>
      refine ⟨S0, Embedding.id S0.C, ?_, ?_, ?_⟩
      · intro x
        rfl
      · ext o
        rfl
      · intro T hT
        simp at hT
  | cons T supports ih =>
      have hbound :
          supportIterationBudget UA VB (T :: supports).length n =
            LocallyTreeLike.fixedSupportBudget UA VB
              (supportIterationBudget UA VB supports.length n) := by
        rfl
      let S0' :
          Stage Control Base Orig Q pOrig
            (LocallyTreeLike.fixedSupportBudget UA VB
              (supportIterationBudget UA VB supports.length n)) := by
        simpa [hbound] using S0
      obtain ⟨Sstep, e0, hp0, hcore0, hcovT⟩ :=
        attachSupport Control Base Orig Q pOrig
          hControl hpOrig hProjected T
          (supportIterationBudget UA VB supports.length n) S0'
      obtain ⟨S1, e1, hp1, hcore1, hcovTail⟩ :=
        ih Sstep
      let e : Embedding S0.C S1.C := e1.comp e0
      refine ⟨S1, e, ?_, ?_, ?_⟩
      · intro x
        calc
          S1.projection (e x) =
              Sstep.projection (e0 x) := hp1 (e0 x)
          _ = S0.projection x := hp0 x
      · rw [hcore1, hcore0]
        rfl
      · intro U hU
        simp only [List.mem_cons] at hU
        rcases hU with hEq | hU
        · subst U
          exact
            CoversSupport.of_embedding
              Control Base Orig Q pOrig hpOrig hProjected
              T e1 hcore1 hcovT
        · exact hcovTail U hU

/-- Every support of a root occurs in the canonical support list. -/
theorem root_support_mem_allSupports
    [Fintype O] [Fintype VB]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    (r : FinalSupport.Root Orig) :
    FinalSupport.Root.support
        Orig Base Q pOrig hpOrig hProjected r ∈
      allSupports (VB := VB) := by
  simp [allSupports]

/-- Uniform final completion: the initial local-tree level depends only on the
requested level and the finite control/base structures, not on the number of
irreducible roots in Orig. -/
theorem build_all_supports
    [Fintype UA] [Fintype VB] [Fintype O]
    (hControl : Control.Irreducible)
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ beta : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = beta b)
    (n : ℕ)
    (hOrigLTL :
      LocallyTreeLike Control Base Orig
        (finalSupportBudget UA VB n)) :
    ∃ S1 : Stage Control Base Orig Q pOrig n,
      IrreduciblesExtendTo Base S1.C := by
  classical
  let supports := allSupports (VB := VB)
  let S0 :
      Stage Control Base Orig Q pOrig
        (supportIterationBudget UA VB supports.length n) :=
    initial Control Base Orig Q pOrig hpOrig (by
      simpa [supports, finalSupportBudget] using hOrigLTL)
  obtain ⟨S1, e, hp, hcore, hcov⟩ :=
    attachSupportList Control Base Orig Q pOrig
      hControl hpOrig hProjected supports n S0
  refine ⟨S1, ?_⟩
  intro R hR
  rcases S1.localized R hR with hInCore | hInBase
  · let inc : Embedding (S1.C.induce R) S1.C :=
      inclusion S1.C R
    let eR : Embedding (S1.C.induce R) Orig :=
      inc.factorThroughRange S1.core hInCore
    let Rng : Set O := Set.range eR
    have hRng : (Orig.induce Rng).Irreducible :=
      hR.range_embedding eR
    let Sfin : Finset O :=
      Finset.univ.filter (fun o => o ∈ Rng)
    have hSset : (↑Sfin : Set O) = Rng := by
      ext o
      simp [Sfin]
    have hSirr :
        (Orig.induce (↑Sfin : Set O)).Irreducible := by
      rw [hSset]
      exact hRng
    let r : FinalSupport.Root Orig := ⟨Sfin, hSirr⟩
    let T : Finset VB :=
      FinalSupport.Root.support
        Orig Base Q pOrig hpOrig hProjected r
    have hTmem : T ∈ supports := by
      exact
        root_support_mem_allSupports
          (Orig := Orig) (Base := Base) (Q := Q) (pOrig := pOrig)
          hpOrig hProjected r
    have hcovT :=
      hcov T hTmem
    let rs :
        FinalSupport.AtSupport
          Orig Base Q pOrig hpOrig hProjected T :=
      ⟨r, rfl⟩
    obtain ⟨beta, hbeta⟩ := hcovT rs
    refine ⟨beta, ?_⟩
    intro z
    have heRmem : eR z ∈ (↑Sfin : Set O) := by
      rw [hSset]
      exact ⟨z, rfl⟩
    let q : ↥(↑Sfin : Set O) := ⟨eR z, heRmem⟩
    refine
      ⟨FinalSupport.Root.toBase
          Orig Base Q pOrig hpOrig hProjected r q, ?_⟩
    have hz := Classical.choose_spec (hInCore z)
    calc
      z.1 = inc z := rfl
      _ = S1.core (eR z) := hz
      _ =
          beta
            (FinalSupport.Root.toBase
              Orig Base Q pOrig hpOrig hProjected r q) := hbeta q
  · exact hInBase

end StructuralRamsey.RelStructure.UniformFinal
