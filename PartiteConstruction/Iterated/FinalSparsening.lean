import PartiteConstruction.Iterated.FinalCompletion
import PartiteConstruction.Ramsey.Basic

/-! # The final sparsening phase

This packages the last paragraph of Appendix A under the hereditary
irreducibility hypothesis exposed by the formalization.

Starting from a finite core \`Orig\`, we keep:
* its embedding into the current extension;
* a homomorphism-embedding of the current extension into the old Ramsey
  witness \`Q\`, agreeing with the original projection on the core;
* the strengthened local-tree invariant;
* localization of every irreducible to the original core or to a copy of
  \`Base\`.

Every irreducible subset of the original core is then processed once.  The
projection determines an embedding of that overlap into a suitable copy of
\`Base\`; a fresh copy of \`Base\` is freely attached.  At the end every
irreducible in the extension lies in a copy of \`Base\`.
-/
namespace StructuralRamsey.RelStructure.FinalSparsening

open FreeAmalgam
open FinalCompletion

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB O Y : Type v}
variable (Control : RelStructure L UA) (Base : RelStructure L VB)
variable (Orig : RelStructure L O) (Q : RelStructure L Y)
variable (n : ℕ) (pOrig : O → Y)

/-- State carried by the final finite attachment phase. -/
structure Stage where
  Vertex : Type v
  finiteVertex : Finite Vertex
  C : RelStructure L Vertex
  core : Embedding Orig C
  projection : Vertex → Y
  projectionHE : C.IsHomomorphismEmbedding Q projection
  core_projection : ∀ o : O, projection (core o) = pOrig o
  locallyTreeLike : LocallyTreeLike Control Base C n
  localized : CoreOrBase (Orig := Orig) (Base := Base) core

attribute [instance] Stage.finiteVertex

/-- Initial state before any final attachment. -/
def initial
    [Finite O]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hOrigLTL : LocallyTreeLike Control Base Orig n) :
    Stage Control Base Orig Q n pOrig where
  Vertex := O
  finiteVertex := inferInstance
  C := Orig
  core := Embedding.id Orig
  projection := pOrig
  projectionHE := hpOrig
  core_projection := fun _ => rfl
  locallyTreeLike := hOrigLTL
  localized := coreOrBase_id

/-- The original subsets already processed by the final attachment phase. -/
def CoversList
    (S : Stage Control Base Orig Q n pOrig)
    (sets : List (Finset O)) : Prop :=
  CoversIrrList (Orig := Orig) (Base := Base) S.core sets

/-- Process an arbitrary finite list of original subsets.  Reducible members
are skipped; an irreducible member is attached using the base copy containing
its image under the original projection. -/
theorem build_list
    [Finite UA] [Finite VB] [Finite O]
    (hControl : HereditarilyIrreducible Control)
    (eControlBase : Embedding Control Base)
    (hBase : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hOrigLTL : LocallyTreeLike Control Base Orig n)
    (sets : List (Finset O))
    (hProjected :
      ∀ (S : Finset O), S ∈ sets →
        (Orig.induce (↑S : Set O)).Irreducible →
        ∃ β : Embedding Base Q,
          ∀ z : ↥(↑S : Set O), ∃ b : VB, pOrig z.1 = β b) :
    ∃ T : Stage Control Base Orig Q n pOrig,
      CoversList Control Base Orig Q n pOrig T sets := by
  classical
  induction sets with
  | nil =>
      let T := initial Control Base Orig Q n pOrig hpOrig hOrigLTL
      refine ⟨T, ?_⟩
      intro S hmem
      simp at hmem
  | cons S₀ sets ih =>
      have hProjectedTail :
          ∀ (S : Finset O), S ∈ sets →
            (Orig.induce (↑S : Set O)).Irreducible →
            ∃ β : Embedding Base Q,
              ∀ z : ↥(↑S : Set O), ∃ b : VB, pOrig z.1 = β b := by
        intro S hmem hS
        exact hProjected S (List.mem_cons_of_mem S₀ hmem) hS
      obtain ⟨T, hCovered⟩ := ih hProjectedTail
      by_cases hS₀ : (Orig.induce (↑S₀ : Set O)).Irreducible
      · obtain ⟨β, hβ⟩ := hProjected S₀ (by simp) hS₀
        let D₀ := Orig.induce (↑S₀ : Set O)
        let fCore : Embedding D₀ T.C :=
          T.core.comp (inclusion Orig (↑S₀ : Set O))
        have hcover :
            ∀ d : ↥(↑S₀ : Set O), ∃ b : VB,
              T.projection (fCore d) = β b := by
          intro d
          obtain ⟨b, hb⟩ := hβ d
          refine ⟨b, ?_⟩
          change T.projection (T.core d.1) = β b
          calc
            T.projection (T.core d.1) =
                pOrig d.1 := T.core_projection d.1
            _ = β b := hb
        obtain ⟨fBase, p, hp, hLocal, hleft, hright⟩ :=
          attachOverIrreducible_preservesProjectionAndLocalTree
            (Control := Control) (Base := Base)
            (D := D₀) (Core := T.C) (Q := Q)
            (fCore := fCore)
            hControl eControlBase hBase hS₀ n
            T.locallyTreeLike T.projection T.projectionHE β hcover
        let Whole := amalgam D₀ T.C Base fCore fBase
        let l := leftEmbedding D₀ T.C Base fCore fBase
        let core' : Embedding Orig Whole := l.comp T.core
        let T' : Stage Control Base Orig Q n pOrig := {
          Vertex := FreeAmalgam.Vertex D₀ T.C Base fCore fBase
          finiteVertex := inferInstance
          C := Whole
          core := core'
          projection := p
          projectionHE := hp
          core_projection := by
            intro o
            calc
              p (core' o) = T.projection (T.core o) := hleft (T.core o)
              _ = pOrig o := T.core_projection o
          locallyTreeLike := hLocal
          localized := by
            exact coreOrBase_amalgam
              (fCurrent := fCore) (fBase := fBase) T.localized
        }
        refine ⟨T', ?_⟩
        have hnew :=
          coversIrrList_amalgam
            (Orig := Orig) (Base := Base) (Current := T.C)
            sets S₀ fBase hCovered
        simpa [CoversList, T', D₀, fCore, Whole, core', l] using hnew
      · refine ⟨T, ?_⟩
        intro S hmem hS
        simp only [List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · subst S
          exact (hS₀ hS).elim
        · exact hCovered S hmem hS

/-- Process every subset of the finite original core.  At the end every
irreducible substructure of the extension is contained in a base copy. -/
theorem build_all
    [Fintype O] [Finite UA] [Finite VB]
    (hControl : HereditarilyIrreducible Control)
    (eControlBase : Embedding Control Base)
    (hBase : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hOrigLTL : LocallyTreeLike Control Base Orig n)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ β : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = β b) :
    ∃ T : Stage Control Base Orig Q n pOrig,
      IrreduciblesExtendTo Base T.C := by
  classical
  let sets : List (Finset O) := (Finset.univ.powerset).toList
  have hProjectedList :
      ∀ (S : Finset O), S ∈ sets →
        (Orig.induce (↑S : Set O)).Irreducible →
        ∃ β : Embedding Base Q,
          ∀ z : ↥(↑S : Set O), ∃ b : VB, pOrig z.1 = β b := by
    intro S _ hS
    exact hProjected (↑S : Set O) hS
  obtain ⟨T, hCovered⟩ :=
    build_list Control Base Orig Q n pOrig
      hControl eControlBase hBase hpOrig hOrigLTL
      sets hProjectedList
  refine ⟨T, ?_⟩
  intro R hR
  rcases T.localized R hR with hCore | hBaseCopy
  · let inc : Embedding (T.C.induce R) T.C := inclusion T.C R
    let eR : Embedding (T.C.induce R) Orig :=
      inc.factorThroughRange T.core hCore
    let Rng : Set O := Set.range eR
    have hRng : (Orig.induce Rng).Irreducible :=
      hR.range_embedding eR
    let S : Finset O := Finset.univ.filter (fun o => o ∈ Rng)
    have hSset : (↑S : Set O) = Rng := by
      ext o
      simp [S]
    have hSirr : (Orig.induce (↑S : Set O)).Irreducible := by
      rw [hSset]
      exact hRng
    have hSmem : S ∈ sets := by
      simp [sets]
    obtain ⟨β, hβ⟩ := hCovered S hSmem hSirr
    refine ⟨β, ?_⟩
    intro z
    have heRmem : eR z ∈ (↑S : Set O) := by
      rw [hSset]
      exact ⟨z, rfl⟩
    let q : ↥(↑S : Set O) := ⟨eR z, heRmem⟩
    obtain ⟨b, hb⟩ := hβ q
    refine ⟨b, ?_⟩
    have hz := Classical.choose_spec (hCore z)
    calc
      z.1 = inc z := rfl
      _ = T.core (eR z) := hz
      _ = β b := hb
  · exact hBaseCopy

/-- The Ramsey arrow of the original core survives the final extension. -/
theorem Stage.arrow
    {κ : Type*}
    (T : Stage Control Base Orig Q n pOrig)
    (h : StructuralRamsey.Arrow Control Base Orig κ) :
    StructuralRamsey.Arrow Control Base T.C κ :=
  h.of_embedding T.core

end StructuralRamsey.RelStructure.FinalSparsening
