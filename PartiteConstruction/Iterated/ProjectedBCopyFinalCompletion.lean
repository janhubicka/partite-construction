import PartiteConstruction.Iterated.ProjectedBCopyControlAttachment
import PartiteConstruction.Iterated.FinalCompletion
import PartiteConstruction.Ramsey.Basic

/-!
# Track E: finite B-saturation preserving a selected relational control HE

Given a finite relational Orig with a selected homomorphism-embedding
pOrig:Orig→Control, assume that the pOrig image of EACH ordinary
irreducible induced source subset is contained in some FULL B-copy
beta:B↪Control. This is stronger than an unrelated external
source-test embedding into B.

The checked one-step projected attachment lemma constructs a compatible
root embedding into B and freely attaches that B-copy while extending
the SAME control HE. Iterating over the FINITELY MANY original subsets
gives one finite C' with:
* full inclusion j:Orig↪C' and pNew∘j=pOrig on every original vertex;
* full Ramsey-arrow preservation under the inclusion;
* homomorphism-embedding pNew:C'→Control;
* INTERNAL B-extension of every irreducible substructure of C'.

No hereditary irreducibility or A↪B assumption and no local-tree
certificate is used: those occur only in the stronger historical
FinalSparsening.build_all which ALSO retains local tree bounds.

THIS DOES NOT show that the actual two-pass tagged 2019 witness has
the selected projected-B compatibility premise, and it does not
preserve its exact small H-relative completion certificates. The
premise and the latter transfer remain separate construction gates.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FreeAmalgam
open StructuralRamsey.RelStructure.FinalCompletion

universe u v
variable {L : RelLanguage.{u}} {O B Q : Type v}
variable (Orig : RelStructure L O)
variable (Base : RelStructure L B)
variable (Control : RelStructure L Q)
variable (pOrig : O → Q)

/-- One intermediate B-saturation stage on exactly the original core. -/
structure Stage where
  Vertex : Type v
  finiteVertex : Finite Vertex
  C : RelStructure L Vertex
  core : Embedding Orig C
  projection : Vertex → Q
  projectionHE : C.IsHomomorphismEmbedding Control projection
  core_projection : ∀ o : O, projection (core o) = pOrig o
  localized : CoreOrBase (Orig := Orig) (Base := Base) core

attribute [instance] Stage.finiteVertex

/-- Initially every irreducible test is contained in the old core. -/
def initial [Finite O]
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig) :
    Stage Orig Base Control pOrig where
  Vertex := O
  finiteVertex := inferInstance
  C := Orig
  core := Embedding.id Orig
  projection := pOrig
  projectionHE := hpOrig
  core_projection := fun _ => rfl
  localized := coreOrBase_id

def CoversList
    (T : Stage Orig Base Control pOrig)
    (sets : List (Finset O)) : Prop :=
  CoversIrrList (Orig := Orig) (Base := Base) T.core sets

/-- Attach one copy for each original irreducible source subset in a
finite list, retaining its exact projected image inside the Control.
The list may include reducible members, which are skipped. -/
theorem build_list
    [Finite O] [Finite B]
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (sets : List (Finset O))
    (hProjected : ∀ S : Finset O, S ∈ sets →
      (Orig.induce (↑S : Set O)).Irreducible →
      ∃ beta : Embedding Base Control,
        ∀ z : (↑S : Set O), ∃ b : B, pOrig z.1 = beta b) :
    ∃ T : Stage Orig Base Control pOrig,
      CoversList Orig Base Control pOrig T sets := by
  classical
  induction sets with
  | nil =>
      let T := initial Orig Base Control pOrig hpOrig
      refine ⟨T, ?_⟩
      intro S hmem
      simp [CoversList] at hmem
  | cons S0 sets ih =>
      have hTail : ∀ S : Finset O, S ∈ sets →
          (Orig.induce (↑S : Set O)).Irreducible →
          ∃ beta : Embedding Base Control,
            ∀ z : (↑S : Set O), ∃ b : B,
              pOrig z.1 = beta b := by
        intro S hmem hS
        exact hProjected S (List.mem_cons_of_mem S0 hmem) hS
      obtain ⟨T, hCovered⟩ := ih hTail
      by_cases hS0 : (Orig.induce (↑S0 : Set O)).Irreducible
      · obtain ⟨beta, hBeta⟩ := hProjected S0 (by simp) hS0
        let Root := Orig.induce (↑S0 : Set O)
        let i : Embedding Root T.C :=
          T.core.comp (inclusion Orig (↑S0 : Set O))
        have hImage : ∀ d : (↑S0 : Set O), ∃ b : B,
            T.projection (i d) = beta b := by
          intro d
          obtain ⟨b, hb⟩ := hBeta d
          refine ⟨b, ?_⟩
          calc
            T.projection (i d) = T.projection (T.core d.1) := rfl
            _ = pOrig d.1 := T.core_projection d.1
            _ = beta b := hb
        obtain ⟨j, pNew, hpNew, hLeft, _hRight, _hOverlap⟩ :=
          attach_irreducible_preserves_controlHE
            hS0 i T.projection T.projectionHE beta hImage
        let Whole := FreeAmalgam.amalgam Root T.C Base i j
        let l := FreeAmalgam.leftEmbedding Root T.C Base i j
        let core' : Embedding Orig Whole := l.comp T.core
        let T' : Stage Orig Base Control pOrig := {
          Vertex := FreeAmalgam.Vertex Root T.C Base i j
          finiteVertex := inferInstance
          C := Whole
          core := core'
          projection := pNew
          projectionHE := hpNew
          core_projection := by
            intro o
            calc
              pNew (core' o) = T.projection (T.core o) :=
                hLeft (T.core o)
              _ = pOrig o := T.core_projection o
          localized := by
            exact coreOrBase_amalgam
              (fCurrent := i) (fBase := j) T.localized
        }
        refine ⟨T', ?_⟩
        have hNew :=
          coversIrrList_amalgam
            (Orig := Orig) (Base := Base) (Current := T.C)
            sets S0 j hCovered
        simpa [CoversList, T', Root, i, Whole, core', l] using hNew
      · refine ⟨T, ?_⟩
        intro S hmem hS
        simp only [List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · subst S
          exact (hS0 hS).elim
        · exact hCovered S hmem hS

/-- Process every original irreducible subset exactly once. The old
source is an induced full substructure of one finite final target;
the same selected HE map to Control and all previously attached
B-copies survive every subsequent free attachment. -/
theorem build_all
    [Fintype O] [Finite B]
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hProjected : ∀ (S : Set O), (Orig.induce S).Irreducible →
      ∃ beta : Embedding Base Control,
        ∀ z : S, ∃ b : B, pOrig z.1 = beta b) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W)
      (j : Embedding Orig C') (pNew : W → Q),
      C'.IsHomomorphismEmbedding Control pNew ∧
      (∀ o : O, pNew (j o) = pOrig o) ∧
      IrreduciblesExtendTo Base C' := by
  classical
  let sets : List (Finset O) := (Finset.univ.powerset).toList
  have hProjectedList : ∀ S : Finset O, S ∈ sets →
      (Orig.induce (↑S : Set O)).Irreducible →
      ∃ beta : Embedding Base Control,
        ∀ z : (↑S : Set O), ∃ b : B, pOrig z.1 = beta b := by
    intro S _ hS
    exact hProjected (↑S : Set O) hS
  obtain ⟨T, hCovered⟩ :=
    build_list Orig Base Control pOrig hpOrig sets hProjectedList
  have hInternal : IrreduciblesExtendTo Base T.C := by
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
      have hSIrr : (Orig.induce (↑S : Set O)).Irreducible := by
        rw [hSset]
        exact hRng
      have hSmem : S ∈ sets := by
        simp [sets]
      obtain ⟨beta, hBeta⟩ := hCovered S hSmem hSIrr
      refine ⟨beta, ?_⟩
      intro z
      have heRmem : eR z ∈ (↑S : Set O) := by
        rw [hSset]
        exact ⟨z, rfl⟩
      let q : (↑S : Set O) := ⟨eR z, heRmem⟩
      obtain ⟨b, hb⟩ := hBeta q
      refine ⟨b, ?_⟩
      have hz := Classical.choose_spec (hCore z)
      calc
        z.1 = inc z := rfl
        _ = T.core (eR z) := hz
        _ = beta b := hb
    · exact hBaseCopy
  exact ⟨T.Vertex, T.finiteVertex, T.C, T.core, T.projection,
    T.projectionHE, T.core_projection, hInternal⟩

/-- The existing Ramsey arrow survives this finite source-side
B-saturation, without changing its colours or its original core. -/
theorem build_all_with_arrow
    [Fintype O] [Finite B]
    {VA : Type v} {A : RelStructure L VA}
    {Color : Type*}
    (hArrow : StructuralRamsey.Arrow A Base Orig Color)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hProjected : ∀ S : Set O, (Orig.induce S).Irreducible →
      ∃ beta : Embedding Base Control,
        ∀ z : S, ∃ b : B, pOrig z.1 = beta b) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W) (pNew : W → Q),
      StructuralRamsey.Arrow A Base C' Color ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      IrreduciblesExtendTo Base C' ∧
      ∃ j : Embedding Orig C',
        ∀ o : O, pNew (j o) = pOrig o := by
  obtain ⟨W, hW, C', j, pNew, hHE, hMap, hInternal⟩ :=
    build_all Orig Base Control pOrig hpOrig hProjected
  exact ⟨W, hW, C', pNew, hArrow.of_embedding j,
    hHE, hInternal, j, hMap⟩

end StructuralRamsey.RelStructure.ProjectedBCopyControl
