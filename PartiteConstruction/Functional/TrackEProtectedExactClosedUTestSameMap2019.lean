import PartiteConstruction.Functional.TrackEClosedExactTaggedTestEmbedding2019
import PartiteConstruction.Ramsey.ClosureClosedMap

/-!
# Track E: selected global tagged protected map yields same-map genuine partial copy

Use the actual corrected tagged closed-U homomorphism-embedding, rather
than inventing a different control map or a canonical tagged test lift.
If the EXACT induced tagged C|S is both U-closed and U-irreducible,
the original f restricts to a FULL tagged embedding on C|S. The
previous exact-test decoder theorem translates that SAME witness to a
full Option(Set) partial-function embedding on S whenever S is closed
under the ACTUAL decoded functions.

This isolates the final geometric task: for every genuine full native
irreducible test E in the final decoded partite target D, prove its
exact image S is U-irreducible in the ACTUAL final tagged C. The U-closed
half is covered by separate Track E #621/#622. No false total-fibre
global reflection or strict native tree is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V W Q : Type v}

/-- EXACT SAME-MAP copy protection from the selected corrected U-HE.
The final test is the actual induced C|S, not a canonical tag of a
reconstructed or hull-enlarged native source. U-irreducibility and
native function-closedness of S remain explicit assumptions. -/
noncomputable def wholeMaskCovered_protectedClosedExactTest_toPartialEmbedding
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (S : Set V)
    (hClosedS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (hUClosedS : IsUClosed (L.wholeMaskClosureRules P) (C.induce S))
    (hUIrredS : IsUIrreducible (L.wholeMaskClosureRules P) (C.induce S))
    (Target : PartialSetStructure L W) [Finite W]
    (part : W → P)
    (hTrans : PartialSetStructure.FibreTransversal Target part)
    (f : V → W)
    (hTagged : IsClosedUHomomorphismEmbedding
      (L.wholeMaskClosureRules P) C
      (wholeMaskTagExpansion (Target.wholeMaskPatternGraph part)) f) :
    ∃ g : PartialSetStructure.Embedding
        (PartialSetStructure.wholeWeakInduce
          ((wholeMaskTagReduct C).wholeMaskPartialDecode) S) Target,
      ∀ x : S, g.toFun x = f x.1 := by
  obtain ⟨j, hj⟩ := hTagged.on_test
    (C.induce S) hUClosedS hUIrredS (inclusion C S)
  let g : PartialSetStructure.Embedding
      (PartialSetStructure.wholeWeakInduce
        ((wholeMaskTagReduct C).wholeMaskPartialDecode) S) Target :=
    wholeMaskCovered_closedExactTaggedTest_toPartialEmbedding
      C Base basePart hC hPos hCover S hClosedS
      Target part hTrans j
  refine ⟨g, ?_⟩
  intro x
  exact hj x

end StructuralRamsey.RelStructure
