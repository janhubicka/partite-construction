import PartiteConstruction.Iterated.ProjectedBCopyProtectedCoveragePreservation
import PartiteConstruction.Iterated.FinalCompletion
import PartiteConstruction.Ramsey.Basic

/-!
# Track E: finite U-closed B-saturation over closed irreducible hulls

The naive finite projected B completion over ordinary irreducible
roots did not preserve U-closedness: these roots need not be closed.
The checked closed-hull B-step from the preceding Track E modules
instead attaches Base along the ambient U-closure of each irreducible
original subset.

The four induction invariants are carried on ONE literal source:
1. global U-closedness;
2. external B-protection for all U-closed U-irreducible tests;
3. the SAME selected ordinary control homomorphism-embedding, unchanged
   on the embedded original core;
4. localization of every ordinary irreducible final test either inside
   that embedded original core or inside an actual attached B-copy.

Each selected original subset can be covered by an attached B-copy
because it is contained in its exact U-closed attachment hull.
After processing ALL original subsets, the localization invariant
gives INTERNAL B-extension of every ordinary irreducible final test.
The Ramsey arrow survives by embedding of the original source.

Premises are explicit: Base U-closed and hereditarily ordinarily
irreducible, original source U-closed and externally B-protected,
selected HE to a control with actual internal B-extension.
No A↪B premise or ordinary hereditary irreducibility of control.

This constructs a RELATIONAL U-closed B-saturation. It does NOT yet
prove that the augmented Qplus remains the canonical whole-mask
tagged expansion of a genuine Option(Set) function structure or that
EVERY original exact weak S of size ≤n still has its H-relative
completion in the augmented source. Those are separate endgame gates.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FreeAmalgam
open StructuralRamsey.RelStructure.FinalCompletion

universe u v
variable {L : RelLanguage.{u}} {O B Q : Type v}

/-- State of the finite closed-hull B-completion, with all certificates
on the SAME current C and the EXACT selected control projection. -/
structure ClosedStage
    (rules : ClosureDescription L)
    (Orig : RelStructure L O)
    (Base : RelStructure L B)
    (Control : RelStructure L Q)
    (pOrig : O → Q) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  C : RelStructure L Vertex
  core : Embedding Orig C
  projection : Vertex → Q
  projectionHE : C.IsHomomorphismEmbedding Control projection
  core_projection : ∀ o : O, projection (core o) = pOrig o
  uClosed : IsUClosed rules C
  externalCover : ∀ {X : Type v} (Test : RelStructure L X),
    IsUClosed rules Test → IsUIrreducible rules Test →
    Embedding Test C → Nonempty (Embedding Test Base)
  localized : CoreOrBase (Orig := Orig) (Base := Base) core

attribute [instance] ClosedStage.finiteVertex

/-- Before attachments, all protected tests are inherited from Orig,
and all ordinary irreducible tests are inside its core. -/
def initialClosedStage
    [Finite O]
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hOrigClosed : IsUClosed rules Orig)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base)) :
    ClosedStage rules Orig Base Control pOrig where
  Vertex := O
  finiteVertex := inferInstance
  C := Orig
  core := Embedding.id Orig
  projection := pOrig
  projectionHE := hpOrig
  core_projection := fun _ => rfl
  uClosed := hOrigClosed
  externalCover := hExternal
  localized := coreOrBase_id

/-- The exact original irreducible subsets already covered by B-copies
in the current source, not only in the external control. -/
def ClosedStageCoversList
    {rules : ClosureDescription L}
    {Orig : RelStructure L O}
    {Base : RelStructure L B}
    {Control : RelStructure L Q}
    {pOrig : O → Q}
    (T : ClosedStage rules Orig Base Control pOrig)
    (sets : List (Finset O)) : Prop :=
  CoversIrrList (Orig := Orig) (Base := Base) T.core sets

/-- One finite induction over ORIGINAL subsets using the full
U-closed, selected-HE and protected-B coverage attachment lemma.
No new weak-test cutoffs or generated substitutes for tested S. -/
theorem build_closed_list
    [Finite O] [Finite B]
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hOrigClosed : IsUClosed rules Orig)
    (hBaseClosed : IsUClosed rules Base)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control)
    (sets : List (Finset O)) :
    ∃ T : ClosedStage rules Orig Base Control pOrig,
      ClosedStageCoversList T sets := by
  classical
  induction sets with
  | nil =>
      let T : ClosedStage rules Orig Base Control pOrig :=
        initialClosedStage Orig Base Control pOrig
          hpOrig hOrigClosed hExternal
      refine ⟨T, ?_⟩
      intro S hmem
      simp [ClosedStageCoversList] at hmem
  | cons S0 sets ih =>
      obtain ⟨T, hCovered⟩ := ih
      by_cases hS0 : (Orig.induce (↑S0 : Set O)).Irreducible
      · let eS0 : Embedding (Orig.induce (↑S0 : Set O)) T.C :=
          T.core.comp (inclusion Orig (↑S0 : Set O))
        let Srange : Set T.Vertex := Set.range eS0
        have hSrange : (T.C.induce Srange).Irreducible :=
          hS0.range_embedding eS0
        obtain ⟨H, hSH, j, pNew, hNewClosed, hNewHE,
            hOldProjection, hNewExternal⟩ :=
          attach_closedHull_preserves_all_three
            T.C Base Control T.projection
            T.uClosed hBaseClosed T.externalCover
            hBaseHered T.projectionHE hControl
            Srange hSrange
        let Root : RelStructure L H := T.C.induce H
        let i : Embedding Root T.C := inclusion T.C H
        let Whole : RelStructure L
            (FreeAmalgam.Vertex Root T.C Base i j) :=
          FreeAmalgam.amalgam Root T.C Base i j
        let l : Embedding T.C Whole :=
          FreeAmalgam.leftEmbedding Root T.C Base i j
        let right : Embedding Base Whole :=
          FreeAmalgam.rightEmbedding Root T.C Base i j
        let core' : Embedding Orig Whole := l.comp T.core
        let T' : ClosedStage rules Orig Base Control pOrig := {
          Vertex := FreeAmalgam.Vertex Root T.C Base i j
          finiteVertex := inferInstance
          C := Whole
          core := core'
          projection := pNew
          projectionHE := hNewHE
          core_projection := by
            intro o
            calc
              pNew (core' o) = T.projection (T.core o) :=
                hOldProjection (T.core o)
              _ = pOrig o := T.core_projection o
          uClosed := hNewClosed
          externalCover := hNewExternal
          localized := by
            exact coreOrBase_amalgam
              (fCurrent := i) (fBase := j) T.localized
        }
        refine ⟨T', ?_⟩
        change CoversIrrList (Orig := Orig) (Base := Base)
          core' (S0 :: sets)
        intro S hmem hIrr
        simp only [List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · subst S
          refine ⟨right, ?_⟩
          intro z
          let w : (↑S0 : Set O) := z
          have hw : eS0 w ∈ H := hSH ⟨w, rfl⟩
          let d : H := ⟨eS0 w, hw⟩
          refine ⟨j d, ?_⟩
          calc
            core' z.1 = l (T.core z.1) := rfl
            _ = l (eS0 w) := rfl
            _ = l (i d) := rfl
            _ = right (j d) :=
              FreeAmalgam.left_right_overlap Root T.C Base i j d
        · obtain ⟨beta, hBeta⟩ := hCovered S hmem hIrr
          refine ⟨l.comp beta, ?_⟩
          intro z
          obtain ⟨b, hb⟩ := hBeta z
          exact ⟨b, congrArg l hb⟩
      · refine ⟨T, ?_⟩
        intro S hmem hIrr
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact (hS0 hIrr).elim
        · exact hCovered S hmem hIrr

/-- Full finite U-closed B saturation: the original finite core embeds
in a new U-closed source carrying the SAME selected HE to Control;
external B-protection persists; EVERY ordinary irreducible test of
the new source has an INTERNAL B-extension. -/
theorem build_closed_all
    [Fintype O] [Finite B]
    {rules : ClosureDescription L}
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    (hOrigClosed : IsUClosed rules Orig)
    (hBaseClosed : IsUClosed rules Base)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W)
      (j : Embedding Orig C') (pNew : W → Q),
      IsUClosed rules C' ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      (∀ o : O, pNew (j o) = pOrig o) ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test C' → Nonempty (Embedding Test Base)) ∧
      IrreduciblesExtendTo Base C' := by
  classical
  let sets : List (Finset O) := (Finset.univ.powerset).toList
  obtain ⟨T, hCovered⟩ :=
    build_closed_list Orig Base Control pOrig
      hOrigClosed hBaseClosed hExternal hBaseHered
      hpOrig hControl sets
  have hInternal : IrreduciblesExtendTo Base T.C := by
    intro R hR
    rcases T.localized R hR with hInCore | hInBase
    · let inc : Embedding (T.C.induce R) T.C :=
        inclusion T.C R
      let eR : Embedding (T.C.induce R) Orig :=
        inc.factorThroughRange T.core hInCore
      let Rng : Set O := Set.range eR
      have hIrredRng : (Orig.induce Rng).Irreducible :=
        hR.range_embedding eR
      let S : Finset O := Finset.univ.filter (fun o => o ∈ Rng)
      have hSset : (↑S : Set O) = Rng := by
        ext o
        simp [S]
      have hSIrr : (Orig.induce (↑S : Set O)).Irreducible := by
        rw [hSset]
        exact hIrredRng
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
      have hz := Classical.choose_spec (hInCore z)
      calc
        z.1 = inc z := rfl
        _ = T.core (eR z) := hz
        _ = beta b := hb
    · exact hInBase
  exact ⟨T.Vertex, T.finiteVertex, T.C, T.core, T.projection,
    T.uClosed, T.projectionHE, T.core_projection,
    T.externalCover, hInternal⟩

/-- The full A/B Ramsey arrow of the ORIGINAL source is retained
in the SAME U-closed, globally controlled, B-covered final source.
No strict function-language tree or weak-H completion is asserted. -/
theorem build_closed_all_with_arrow
    [Fintype O] [Finite B]
    {rules : ClosureDescription L}
    {VA : Type v} (A : RelStructure L VA)
    (Orig : RelStructure L O) (Base : RelStructure L B)
    (Control : RelStructure L Q) (pOrig : O → Q)
    {Color : Type*}
    (hArrow : StructuralRamsey.Arrow A Base Orig Color)
    (hOrigClosed : IsUClosed rules Orig)
    (hBaseClosed : IsUClosed rules Base)
    (hExternal : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test Orig → Nonempty (Embedding Test Base))
    (hBaseHered : HereditarilyIrreducible Base)
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo Base Control) :
    ∃ (W : Type v) (_ : Finite W)
      (C' : RelStructure L W) (pNew : W → Q),
      StructuralRamsey.Arrow A Base C' Color ∧
      IsUClosed rules C' ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      IrreduciblesExtendTo Base C' ∧
      ∃ j : Embedding Orig C',
        (∀ o : O, pNew (j o) = pOrig o) := by
  obtain ⟨W, hW, C', j, pNew, hCClosed, hpNew,
      hCore, _hExternal, hInternal⟩ :=
    build_closed_all Orig Base Control pOrig
      hOrigClosed hBaseClosed hExternal hBaseHered
      hpOrig hControl
  exact ⟨W, hW, C', pNew, hArrow.of_embedding j,
    hCClosed, hpNew, hInternal, j, hCore⟩

end StructuralRamsey.RelStructure.ProjectedBCopyControl
