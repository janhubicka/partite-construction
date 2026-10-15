import PartiteConstruction.Functional.EHNMaximalMixedHardRootReduction
import PartiteConstruction.Functional.EHNOriginalPartialMaximalMixedFromTwo

/-!
# Complete strict original-2019 n-pass functional sparsening: hard-root frontier

The full n-pass original partial-function sparsening construction was
proved in the existing reusable EHN library, conditional on a uniform
maximal-mixed relative B-tree extension assertion. Rooted finite Ramsey
canonicalization, all Hales--Jewett powers, the pure sides, generator
rank drops and the final B-attachment were already machine checked.

A new exact native theorem constructs BOTH required relative extensions
automatically whenever the actual common closed separator is generated
by at most one vertex, irrespective of its often much larger cardinality.

Therefore the FULL n-pass strict functional sparsening conclusion follows
from the narrowly isolated hypothesis: genuinely mixed maximal projected
generator-rank native tests of rank >=2 whose actual common root itself
requires >=2 generators admit compatible relative strict B-tree targets.
No such higher-rank rooted extension is assumed to have been proved.

This conditional theorem is the published Appendix A proof architecture
expressed with exact closed full-functional test rank rather than a false
weak-test completion or total-fibre global homomorphism.
-/

namespace StructuralRamsey.FunctionalPartite.EHN.StrictRanked

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V : Type v}

/-- The exact remaining relative completion request in the verified
strict original partial-function native iterated construction:
maximal mixed tests at rank >=2 whose common root needs >=2 generators. -/
def MaximalMixedHardRootSchemaFromTwo
    (K : Structure.StructureClass (L := L))
    (A : Structure L U) (Base : Structure L V) : Prop :=
  ∀ (Q : Type v) [Finite Q] [DecidableEq Q]
    (Control : Structure L Q) (n : ℕ),
    2 ≤ n →
    ∀ (Old T : EHN.Stage K Control)
      (alpha : Structure.Embedding A Control)
      (f : FunctionalPartite.Embedding
        (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
          (Old.system.weak_support_closed
            Control Old.isPartite.1 A alpha))
        T.system),
      LocallyGeneratedOriginalPartialTreeCompletable
        Base Old.system.toStructure n →
      LocallyGeneratedOriginalPartialTreeCompletable
        Base T.system.toStructure n →
      Attachment.NativeMaximalMixedHardRootRelativeExtension
        Old.system (Old.system.support alpha.toFunctionEmbedding)
        (Old.system.weak_support_closed
          Control Old.isPartite.1 A alpha)
        T.system f Base n


/-- The original uniform maximal mixed-root schema restricted to n>=2
follows from the strictly weaker hard-root requirement. One-generated
roots are already completed by the verified native full-functional
relative B-tree construction; no unproved root gluing is used here. -/
theorem MaximalMixedSchemaFromTwo.of_hardRoot
    {K : Structure.StructureClass (L := L)}
    {A : Structure L U} {Base : Structure L V}
    (hBase : Base.Irreducible)
    (eAB : Structure.Embedding A Base)
    (hHard : MaximalMixedHardRootSchemaFromTwo K A Base) :
    MaximalMixedSchemaFromTwo K A Base := by
  intro Q _ _ Control n h2 Old T alpha f hOld hCore
  exact Attachment.NativeMaximalMixedOriginalPartialRelativeExtension.of_hardRoot
    Old.system Control Old.isPartite A Base hBase eAB
    alpha T.system f n hCore hOld
    (hHard Q Control n h2 Old T alpha f hOld hCore)

/-- The entire full-functional n-pass Ramsey and final B-copy
sparsening construction is now verified conditional ONLY on hard
roots needing at least TWO generators in genuinely mixed maximal
rank-n tests. Original-2019 partial projection, strict full-functional
closed vertex-n B-trees and irreducible B-coverage are retained.

The compatible hard-root extensions themselves remain to be
constructed. In particular, no complete-fibre homomorphism is claimed. -/
theorem sparsening_of_hard_root_schema_from_two
    {P : Type v}
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hHard : MaximalMixedHardRootSchemaFromTwo K A Base)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A Base C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      LocallyClosedOriginalPartialTreeCompletable Base C n ∧
      IrreduciblesExtendTo Base C ∧
      LooseTreeAmalgam Base W C := by
  exact sparsening_of_maximal_mixed_schema_from_two
    K hK A Base D hKA hKB hBIrr hPos eAB
    κ hArrow
    (MaximalMixedSchemaFromTwo.of_hardRoot hBIrr eAB hHard) n hn

end StructuralRamsey.FunctionalPartite.EHN.StrictRanked
