import PartiteConstruction.Functional.TrackCRichActualExactFullCopyUIrred2019
import PartiteConstruction.Functional.TrackCRichExactFullTarget
import PartiteConstruction.Ramsey.ClosureClosedMap

/-!
# Track C: the SAME selected protected OLD map is FULL on rich E-copies

In the actual corrected first-stage 2019 tagged witness C, the
genuinely partial decoder P retains some(empty) vs none. A second
rich functional EHN cover supplies an ORIGINAL source-defined
homomorphism-embedding q:D→P; q is NOT globally full.

Fix the ACTUAL selected OLD H-target map f:C.induce S→tag(Target).
It is globally positive and FULL on U-closed U-irreducible tests.
For any full domain-aware irreducible E↪D with q[E]⊆S:
* q is FULL on E by the real rich HE hypothesis;
* the full q-image R is genuinely function-closed, with no hull;
* the exact actual tagged C.induce R is U-closed U-irreducible by
  the rich source/OLD dictionary (Track C #730);
* f is FULL on that exact tagged R by protectedness;
* the checked exact FULL tagged-to-partial decoder (#715) yields
  a FULL genuinely partial E↪Target on the literal f∘q∘e map.

The map and the H-target are not chosen anew for individual E-tests.
The original full Option(Set) semantics are retained throughout.
This theorem is the rich full-on-irreducibles HALF of the selected
same-H target completion. The global positive half remains separate.

We use the library's equivalent abstract closed-U-test map
predicate. In the corrected survey the original 2019 induced map
predicate is equivalent to it by the already verified ATR
InducedClosed2019TestNormalization, rather than by an axiom here.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q X Y T : Type v}

/-- A single selected protected OLD map f on an EXACT containing
weak S is FULL after composing with the selected ORIGINAL genuine
partial HE q on every exact rich irreducible E-copy, into the
SAME H target and on the literal f∘q∘e vertices. No
NoDefinedEmptyValues assumption. -/
theorem wholeMaskCovered_selectedRichFullTest_to_sameTarget
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (D : PartialSetStructure L X) (q : X → V)
    (hq : D.IsOptionClosedFreeHomomorphismEmbedding
      (wholeMaskOriginalDecode C) q)
    (S : Set V)
    (Target : PartialSetStructure L Y) [Finite Y]
    (targetPart : Y → Parts)
    (hTrans : FibreTransversal Target targetPart)
    (f : S → Y)
    (hf : IsClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S)
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f)
    (E : PartialSetStructure L T)
    (hE : E.IsOptionClosedFreeIrreducible)
    (e : PartialSetStructure.Embedding E D)
    (hImageS : ∀ z : T, q (e.toFun z) ∈ S) :
    ∃ k : PartialSetStructure.Embedding E Target,
      ∀ z : T, k.toFun z = f ⟨q (e.toFun z), hImageS z⟩ := by
  classical
  obtain ⟨g, hg⟩ := hq.2 E hE e
  let R : Set V := Set.range g.toFun
  have hRangeIn : R ⊆ S := by
    rintro y ⟨x, rfl⟩
    rw [hg x]
    exact hImageS x
  have hOriginalClosed :
      (wholeMaskOriginalDecode C).IsClosed R :=
    g.range_isClosed
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  have hPlusClosed : Plus.IsClosed R := by
    intro F xs U hxs hVal
    exact hOriginalClosed F.down xs U hxs hVal
  have hTaggedClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce R) :=
    (wholeMaskCovered_inducedUClosed_iff_decodedClosed
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover R).mpr hPlusClosed
  have hTaggedIrred :
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce R) :=
    wholeMaskCovered_exactRichIrredCopy_taggedUIrreducible
      C Base basePart hC hPos hCover E hE g
  let i : Embedding (C.induce R) (C.induce S) := {
    toFun := fun z => ⟨z.1, hRangeIn z.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : S => z.1) hxy
    map_rel_iff := by intro R xs; rfl
  }
  obtain ⟨jTag, hjTag⟩ :=
    hf.on_test (C.induce R) hTaggedClosed hTaggedIrred i
  obtain ⟨k, hk⟩ :=
    wholeMaskCovered_exactRichPartialTest_toFullTarget
      C Base basePart hC hPos hCover
      E g Target targetPart hTrans jTag
  refine ⟨k, ?_⟩
  intro z
  have hPoint :
      i ⟨g.toFun z, ⟨z, rfl⟩⟩ =
        (⟨q (e.toFun z), hImageS z⟩ : S) := by
    apply Subtype.ext
    exact hg z
  calc
    k.toFun z = jTag.toFun ⟨g.toFun z, ⟨z, rfl⟩⟩ :=
      hk z
    _ = f (i ⟨g.toFun z, ⟨z, rfl⟩⟩) := hjTag _
    _ = f ⟨q (e.toFun z), hImageS z⟩ :=
      congrArg f hPoint

end StructuralRamsey.RelStructure
