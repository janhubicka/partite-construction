import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.TrackEPartialFullEmbeddingCollapse2019
import PartiteConstruction.Iterated.FinalAttachment
import PartiteConstruction.Ramsey.ClosureUIrreducible2019

/-!
# Track E: INTERNAL tagged canonical B copies decode into INTERNAL native B copies

The corrected two-pass 2019 U-closed, canonical-B-covered tagged target C
need not itself be a syntactically canonical whole-mask expansion.
Nevertheless a FULL embedding of the genuine canonical with-parts tagged
B into C forgets fresh tags to a FULL embedding of whole-mask OLD graphs.
The already verified covered-decoder theorem converts this to a FULL
genuine Option(Set)-valued partial-function embedding on the SAME map
and SAME vertices, preserving the recovered target part map. The
generic checked full embedding collapse forgets only undefined-vs-
defined-empty information to produce a FULL native set-valued-function
embedding.

Thus a SOURCE-side internal B-copy really is an internal native copy;
it cannot be replaced by the weaker external Test↪Tag(B) certificate.

A second theorem handles the key source class geometry: if a tested
exact vertex subset S is U-closed and U-irreducible in actual C, and
K contains canonical Tag(B), is closed-U hereditary and each K-member
is ordinarily irreducible, protected B-cover makes the literal
C.induce S ordinary irreducible. The INTERNAL Btag extension
then yields a genuine native full B-copy containing S.

This removes any assumption that a closed U-irreducible test is
automatically ordinarily irreducible. The claim uses K explicitly.
No strict native B-tree local completion is implied.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {X W : Type v}

/-- INTERNAL Btag coverage of every ordinarily irreducible exact
tagged source subset produces a full INTERNAL native B-copy
on precisely the same carrier and selected embedding map. -/
theorem wholeMaskCovered_internalTaggedB_to_native_of_ordinaryIrred
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L X) [Finite X]
    (basePart : X → P)
    (hTrans : FibreTransversal Base basePart)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hInternal :
      IrreduciblesExtendTo
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)) C)
    (S : Set W) (hSIrred : (C.induce S).Irreducible) :
    ∃ beta : Structure.Embedding Base.collapseDomain
        (wholeMaskOriginalDecode C).collapseDomain,
      ∀ z : S, ∃ x : X, z.1 = beta x := by
  classical
  obtain ⟨betaTag, hBetaTag⟩ := hInternal S hSIrred
  let betaOld : Embedding (withPartsWholeMaskOld Base basePart)
      (wholeMaskTagReduct C) :=
    betaTag.wholeMaskTagReduct
  let betaPartial :
      PartPreservingEmbedding Base basePart
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C Base basePart hC hCover) :=
    PartialSetStructure.Embedding.ofCoveredPartiteWholeMaskOld
      Base basePart hTrans C Base basePart hC hPos hCover betaOld
  let betaNative : Structure.Embedding Base.collapseDomain
      (wholeMaskOriginalDecode C).collapseDomain :=
    betaPartial.1.collapseDomain
  refine ⟨betaNative, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := hBetaTag z
  exact ⟨x, hx⟩

/-- Protected external B-coverage and closed-U K-hereditariness
promote a CLOSED U-irreducible exact tagged test to an ordinary
irreducible tagged test; the internal Btag covering law then
gives an INTERNAL genuine native B-copy containing it.

This is exactly the missing non-Gaifman shortcut in the functional
2019 internally B-saturated endgame. -/
theorem wholeMaskCovered_internalTaggedB_to_native_of_closedUIrred
    {K : StructureClass.{u,v}
      (L := (L.withParts P).wholeMaskTagLanguage P)}
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) W)
    (Base : PartialSetStructure L X) [Finite X]
    (basePart : X → P)
    (hTrans : FibreTransversal Base basePart)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hBaseK : K (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hHer : ClosedUHereditary K
      ((L.withParts P).wholeMaskClosureRules P))
    (hKIrr : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      K Test → Test.Irreducible)
    (hCover : ∀ {T : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) T),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hInternal :
      IrreduciblesExtendTo
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)) C)
    (S : Set W)
    (hSClosed : IsUClosed ((L.withParts P).wholeMaskClosureRules P)
      (C.induce S))
    (hSUIrred : IsUIrreducible
      ((L.withParts P).wholeMaskClosureRules P) (C.induce S)) :
    ∃ beta : Structure.Embedding Base.collapseDomain
        (wholeMaskOriginalDecode C).collapseDomain,
      ∀ z : S, ∃ x : X, z.1 = beta x := by
  obtain ⟨eB⟩ := hCover (C.induce S) hSClosed hSUIrred
    (inclusion C S)
  have hSK : K (C.induce S) :=
    hHer (C.induce S)
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart))
      hBaseK hSClosed eB
  have hOrdIrred : (C.induce S).Irreducible :=
    hKIrr (C.induce S) hSK
  exact wholeMaskCovered_internalTaggedB_to_native_of_ordinaryIrred
    C Base basePart hTrans hC hPos hCover hInternal S hOrdIrred

end StructuralRamsey.RelStructure
