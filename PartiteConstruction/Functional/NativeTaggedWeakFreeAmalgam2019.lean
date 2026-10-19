import PartiteConstruction.Functional.NativePatternGraphFreeAmalgam2019
import PartiteConstruction.Iterated.WeakFreeAmalgamInduce

/-!
# Every EXACT weak test of a native free functional attachment retains
# its full AMBIENT 2019 U-pattern source free-amalgam diagram

The native full function-language free-amalgam diagram translates
to a full tagged OLD equality-pattern U-closure diagram with the
SAME vertices (NativePatternGraphFreeAmalgam2019). Restrict that
relational diagram to ANY exact weak source vertex set S using the
previously proved relational IsFreeAmalgam.weakInduce_withMaps.

All ambient domain/root tags and function graph/output tuples
remain induced from the ORIGINAL source structure; none are
recomputed from function fibres truncated to S. The two side
tests are the literal inverse images iL⁻¹S, iR⁻¹S, and their
common root (iL∘sL)⁻¹S. The resulting tagged relation
structures are connected by full embeddings and still freely
amalgamate along the exact weak common root.

The source vertex set and all three side/root cardinalities
are preserved. This is the precise source-side counterpart of
weak U-substructure induction in the corrected 2019 proof. It
does NOT assert that independently constructed strict functional
B-tree TARGET completions of the two sides have compatible
root profiles.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}

/-- Full source-side 2019 U-pattern free-amalgam diagram on the
exact induced ambient tagged weak tests of ANY genuine native
full functional free attachment.

Every side/root map is a FULL tagged relational embedding on
the precise inverse-image vertex set and the output diagrams
carry no generated closure hull. -/
theorem taggedPatternGraph_exactWeak_withMaps
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    let TagRoot := RelStructure.patternTagExpansion Root.patternGraph
    let TagLeft := RelStructure.patternTagExpansion Left.patternGraph
    let TagRight := RelStructure.patternTagExpansion Right.patternGraph
    let TagWhole := RelStructure.patternTagExpansion Whole.patternGraph
    ∃ (mL : RelStructure.Embedding
        (TagRoot.induce Mset) (TagLeft.induce Lset))
      (mR : RelStructure.Embedding
        (TagRoot.induce Mset) (TagRight.induce Rset))
      (jL : RelStructure.Embedding
        (TagLeft.induce Lset) (TagWhole.induce S))
      (jR : RelStructure.Embedding
        (TagRight.induce Rset) (TagWhole.induce S)),
      RelStructure.IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL a).1 = iL a.1) ∧
      (∀ b : Rset, (jR b).1 = iR b.1) := by
  exact (hFree.taggedPatternGraph).weakInduce_withMaps S

end StructuralRamsey.Structure.IsFreeAmalgam
