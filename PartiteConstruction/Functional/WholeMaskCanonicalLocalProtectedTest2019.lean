import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019
import PartiteConstruction.Ramsey.ClosureClosedMap

/-!
# Genuine functional copies on protected exact 2019 weak local tests

This is the FULL-EMBEDDING half of local K-completion transfer on
an explicitly protected canonical functional test.  Assume that a
full-root canonical tagged partial-function test A embeds into the
EXACT induced weak relational source C.induce S, and that this test is
U-irreducible.  A corrected 2019 CLOSED-U local completion map into
a canonical genuine functional target must then carry this test to
a FULL genuinely partial, part-preserving functional embedding.

The map agrees literally on original vertices with the local
completion map, without taking any closure of S.  Defined-empty
operations, undefined operations and all whole-valued outputs are
fully reflected on the protected copy.

This does NOT show every intrinsically irreducible weak functional
test admits an ambient canonical tagged lift or that an arbitrary
K-member target is canonical.  Both are separate obligations.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

/-- The existing 2019 protected closed U-irreducible copy axiom gives
a FULL original partial-function part-preserving embedding whenever
the tested canonical copy is genuinely present in the exact weak
tagged source.  The source C need NOT be canonical; the target IS. -/
theorem canonicalProtectedTest_of_closedULocalHE
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (S : Set V)
    (Target : PartialSetStructure L X) [Finite X]
    (targetPart : X → P)
    (hTransTarget : FibreTransversal Target targetPart)
    (f : S → X)
    (hLocal : IsClosedUHomomorphismEmbedding
      ((L.withParts P).wholeMaskClosureRules P)
      (C.induce S)
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f)
    (A : PartialSetStructure L W) [Finite W]
    (partA : W → P)
    (hTransA : FibreTransversal A partA)
    (hUIrred : IsUIrreducible
      ((L.withParts P).wholeMaskClosureRules P)
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)))
    (e : RelStructure.Embedding
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      (C.induce S)) :
    ∃ g : PartPreservingEmbedding A partA Target targetPart,
      ∀ x : W, g.1.toFun x = f (e x) := by
  classical
  have hTransPlus : FibreTransversal (A.withParts partA) partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTransA
  have hClosed : IsUClosed
      ((L.withParts P).wholeMaskClosureRules P)
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) :=
    (A.withParts partA).wholeMaskTagExpansion_isUClosed
      partA hTransPlus
  obtain ⟨gTag, hgTag⟩ :=
    hLocal.on_test
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      hClosed hUIrred e
  let gOld : RelStructure.Embedding
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld Target targetPart) :=
    gTag.wholeMaskTagReduct
  refine ⟨PartPreservingEmbedding.decode hTransA hTransTarget gOld, ?_⟩
  intro x
  change gTag x = f (e x)
  exact hgTag x

end StructuralRamsey.PartialSetStructure
