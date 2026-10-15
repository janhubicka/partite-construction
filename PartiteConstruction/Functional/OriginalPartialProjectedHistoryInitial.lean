import PartiteConstruction.Functional.OriginalPartialProjectedHistoryInvariant
import PartiteConstruction.Functional.InitialTreeCompletion
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Full original-partial projected-history witnesses from STRICT B-trees

The historical published sparsening argument begins with a genuine
strict B-tree of the initial copied B-placements. The new
original-2019 partial-function projected-history invariant must be
established for this initial stage, not simply postulated in a
Picture-preservation assumption.

A strict full-functional B-tree itself supplies a witness for every
genuinely CLOSED test at every generator rank: choose the full
inclusion as the global original-partial map. Its injectivity
remembers EVERY finite projected history, while irreducibility of
each closed partial A-copy locates it in one B constituent.

This file reuses the already verified `EHN.initial_tree`; it does NOT
build any fresh Ramsey/Hales--Jewett stage, change the manuscript
text, or assert the unresolved mixed attachment step.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W VB : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L VB}

namespace FunctionalOriginalPartialProjectedHistoryTreeLike

/-- Strict B-tree sources already have the complete ORIGINAL-PARTIAL
projected A-history invariant, provided every function-closed
substructure of A is irreducible.

For each test choose its full inclusion into C, regarded as an
original-2019 partial map. Thus all projected diary predicates
are preserved by injectivity. For a full partial A-copy, irreducibility
locates it in a constituent Base-copy even when C has many pieces.
The target remains the exact original strict functional B-tree. -/
theorem of_tree
    (hBase : Base.Irreducible)
    (hAclosed : ∀ (H : Set U) (hH : A.IsClosed H),
      (A.induce H hH).Irreducible)
    (hTree : TreeAmalgam Base W C)
    (p : W → P) (n : ℕ) :
    FunctionalOriginalPartialProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  intro S hS _hGen history
  let inc : Embedding (C.induce (↑S : Set W) hS) C :=
    inclusion C (↑S : Set W) hS
  have hPartial : IsOriginalPartialHomomorphismEmbedding
      (C.induce (↑S : Set W) hS) C inc :=
    inc.isEHNHomomorphismEmbedding.toOriginalPartial
  refine ⟨W, C, hTree, inc, hPartial, ?_, ?_⟩
  · intro β H hH e _hProj hRange
    obtain ⟨baseCopy, hContains⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy
        (hAclosed H hH) e
    refine ⟨e, ?_, ?_⟩
    · intro x
      rfl
    · exact ⟨VB, Base, hBase, baseCopy, hContains⟩
  · intro K _hK x y hxy
    have hEq : x = y := inc.injective hxy
    subst y
    exact Iff.rfl

end FunctionalOriginalPartialProjectedHistoryTreeLike
end StructuralRamsey.Structure


namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The ACTUAL positive-arity native initial Picture has full
strict-original-partial B-tree completion of every closed generated
test while simultaneously preserving ALL closed partial A-copies and
arbitrary projected history diaries, at EVERY rank.

The input B-placement is only used by the existing verified
`initial_tree`; no extra construction is needed. -/
theorem initial_originalPartial_projectedHistory
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U)
    (hAclosed : ∀ (H : Set U) (hH : A.IsClosed H),
      (A.induce H hH).Irreducible)
    (Base : Structure L V) [Finite V] [Finite P]
    (hBaseMem : K Base)
    (hBaseIrred : Base.Irreducible)
    (hpos : L.PositiveFuncArity)
    (beta0 : Structure.Embedding Base D)
    (n : ℕ) :
    ∃ T : Stage K D,
      Structure.FunctionalOriginalPartialProjectedHistoryTreeLike
        (A := A) (D := D) (C := T.system.toStructure) (Base := Base)
        T.system.part n ∧
      ∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x := by
  obtain ⟨T, hTree, hCopies⟩ :=
    initial_tree hK Base hBaseMem hBaseIrred hpos beta0
  have hHistory :
      Structure.FunctionalOriginalPartialProjectedHistoryTreeLike
        (A := A) (D := D) (C := T.system.toStructure) (Base := Base)
        T.system.part n :=
    Structure.FunctionalOriginalPartialProjectedHistoryTreeLike.of_tree
      hBaseIrred hAclosed hTree T.system.part n
  exact ⟨T, hHistory, hCopies⟩

end StructuralRamsey.FunctionalPartite.EHN
