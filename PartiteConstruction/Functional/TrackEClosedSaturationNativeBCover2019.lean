import PartiteConstruction.Functional.TrackEInternalTaggedBCopyNativeDescent2019
import PartiteConstruction.Iterated.ProjectedBCopyClosedFiniteSaturation
import PartiteConstruction.Ramsey.Basic

/-!
# Track E: one-source closed B-saturation and native internal B-copy descent

The English proof precedes this Lean statement in
docs/track-e-closed-saturation-native-cover-20261115.md.

Starting from one ACTUAL whole-mask tagged source, this theorem:
* uses the checked finite closed-hull B-saturation with a literal
  selected ordinary homomorphism-embedding into the SAME control;
* retains external U-closed U-irreducible test B-coverage and the
  full tagged Ramsey arrow on the SAME enlarged tagged witness;
* converts internal tagged B-extension on closed U-irreducible tests
  into actual full original native B embeddings, keeping vertices.

K and its closed-U heredity/ordinary irreducibility are explicit.
No claim about native strict B-tree completions or H-membership.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure.ProjectedBCopyControl

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {X W Q VA : Type v}

/-- A conditional *constructive* native internal B-cover endpoint of the
finite U-closed selected-control saturation. All output clauses refer
to the SAME enlarged tagged source and selected map. -/
theorem wholeMask_closedSaturation_internalNativeBCover
    (Base : PartialSetStructure L X) [Finite X]
    (basePart : X → P)
    (hTrans : FibreTransversal Base basePart)
    (hPos : L.PositiveFuncArity)
    (Orig : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    [Fintype W]
    (Control : RelStructure ((L.withParts P).wholeMaskTagLanguage P) Q)
    (pOrig : W → Q)
    (hOrigClosed : IsUClosed
      ((L.withParts P).wholeMaskClosureRules P) Orig)
    (hBaseClosed : IsUClosed
      ((L.withParts P).wholeMaskClosureRules P)
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hBaseHered : HereditarilyIrreducible
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hExternal : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test Orig →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hpOrig : Orig.IsHomomorphismEmbedding Control pOrig)
    (hControl : IrreduciblesExtendTo
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart))
      Control)
    {K : StructureClass
      (L := (L.withParts P).wholeMaskTagLanguage P)}
    (hBaseK : K (wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hHer : ClosedUHereditary K
      ((L.withParts P).wholeMaskClosureRules P))
    (hKIrr : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      K Test → Test.Irreducible)
    (A : RelStructure ((L.withParts P).wholeMaskTagLanguage P) VA)
    (Color : Type*)
    (hArrow : StructuralRamsey.Arrow A
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart))
      Orig Color) :
    ∃ (V' : Type v) (_ : Finite V')
      (C' : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V')
      (j : Embedding Orig C') (pNew : V' → Q),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) C' ∧
      C'.IsHomomorphismEmbedding Control pNew ∧
      (∀ x : W, pNew (j x) = pOrig x) ∧
      (∀ {T : Type v}
        (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
        IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
        IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
        Embedding Test C' →
        Nonempty (Embedding Test
          (wholeMaskTagExpansion
            ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) ∧
      IrreduciblesExtendTo
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))
        C' ∧
      (∀ S : Set V',
        IsUClosed ((L.withParts P).wholeMaskClosureRules P)
          (C'.induce S) →
        IsUIrreducible ((L.withParts P).wholeMaskClosureRules P)
          (C'.induce S) →
        ∃ beta : Structure.Embedding Base.collapseDomain
          (wholeMaskOriginalDecode C').collapseDomain,
          ∀ z : S, ∃ x : X, z.1 = beta x) ∧
      StructuralRamsey.Arrow A
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))
        C' Color := by
  classical
  let Btag : RelStructure
      ((L.withParts P).wholeMaskTagLanguage P) X :=
    wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)
  obtain ⟨V', hV', C', j, pNew, hCClosed, hPNew, hOld,
      hExtNew, hInternal⟩ :=
    ProjectedBCopyControl.build_closed_all
      Orig Btag Control pOrig
      hOrigClosed hBaseClosed hExternal hBaseHered hpOrig hControl
  have hNative : ∀ S : Set V',
      IsUClosed ((L.withParts P).wholeMaskClosureRules P)
        (C'.induce S) →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P)
        (C'.induce S) →
      ∃ beta : Structure.Embedding Base.collapseDomain
          (wholeMaskOriginalDecode C').collapseDomain,
        ∀ z : S, ∃ x : X, z.1 = beta x := by
    intro S hClosed hUIrr
    exact wholeMaskCovered_internalTaggedB_to_native_of_closedUIrred
      (K := K) C' Base basePart hTrans hCClosed hPos
      hBaseK hHer hKIrr hExtNew hInternal S hClosed hUIrr
  exact ⟨V', hV', C', j, pNew, hCClosed, hPNew, hOld,
    hExtNew, hInternal, hNative, hArrow.of_embedding j⟩

end StructuralRamsey.RelStructure
