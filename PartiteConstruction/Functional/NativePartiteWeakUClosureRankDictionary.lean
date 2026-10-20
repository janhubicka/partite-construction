import PartiteConstruction.Functional.NativeWeakAmbientUClosureDictionary
import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge

/-!
# Closure and rank for the weak restriction retaining surviving outputs

For any literal weak vertex subset S of a genuine transversal
multivalued functional partite system B, the original weak
function-closed predicates on every T⊆S are equal to those
for the per-output-part SINGLETON split.

The generic positive-arity weak-ambient-tag dictionary then
identifies native weak closedness with relative 2019 U-substructure
closedness of the induced AMBIENT complete-root tagged split
structure E|S. Thus the entire weak relative closure operator
and intrinsic minimum generating cardinality are preserved on
EXACTLY S, even if S is not function-closed in B.

Throughout, `weakInduce` intersects each ambient output fibre with S.
It does not delete an entire application when only part of its fibre leaves S.
Output-part splitting preserves the former operation; it need not preserve
the latter. This theorem therefore does not identify the whole-fibre weak
restriction with the induced ambient tagged structure.

The ambient OLD function-domain tags remain present when
all corresponding actual outputs leave S; the intermediate
source is U-SEMI-CLOSED, not falsely U-CLOSED. The source-side
dictionary is independent of the unresolved strict functional
target B-tree root-profile synchronization.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- On any exact weak vertex set S, being closed under
surviving ORIGINAL multivalued function values is exactly
being closed under ALL surviving per-output-part singleton
values. The statement is uniform over every T⊆S.

No ambient closure hull is taken; native weak function fibres
are literally filtered by membership in S. -/
theorem System.weakIsClosed_iff_split_weakIsClosed
    (B : System L P V) (S : Set V) (T : Set S) :
    (B.toStructure.weakInduce S).IsClosed T ↔
      ((B.splitOutputParts).toStructure.weakInduce S).IsClosed T := by
  constructor
  · intro hClosed Fq xs hxs y hy
    exact hClosed Fq.1.down xs hxs hy.1
  · intro hClosed F xs hxs y hy
    exact hClosed (ULift.up F, B.part y.1)
      xs hxs ⟨hy, rfl⟩

/-- Exact weak multi-output native function-closedness is
equivalent to relative U-closedness of the AMBIENT tagged
singleton split structure induced on the SAME weak S.

Original active input/domain records are retained even when
the corresponding output was omitted from S. -/
theorem System.weakIsClosed_iff_outputTagged_isUSubstructure
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (T : Set S) :
    (B.toStructure.weakInduce S).IsClosed T ↔
      IsUSubstructure (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) T :=
  (B.weakIsClosed_iff_split_weakIsClosed S T).trans
    (Structure.weakIsClosed_iff_ambientTagged_isUSubstructure
      (B.splitOutputParts).toStructure hPos.outputPartIndexed S T)

/-- The exact weak functional closure hull INSIDE S in the
original multivalued language equals the relative U-closure
hull inside the induced AMBIENT tagged singleton language,
with the SAME weak vertex carrier S and seed T.

This is NOT the ambient closure of T in the original whole B. -/
theorem System.weakFunctionClosure_eq_outputTaggedUClosureHull
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (T : Set S) :
    (B.toStructure.weakInduce S).functionClosure T =
      UClosureHull (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) T := by
  have hClosedEquiv (Q : Set S) :
      (B.toStructure.weakInduce S).IsClosed Q ↔
        IsUSubstructure (L.outputPartIndexed P).patternClosureRules
          ((patternTagExpansion
            (B.splitOutputParts).toStructure.patternGraph).induce S) Q :=
    B.weakIsClosed_iff_outputTagged_isUSubstructure hPos S Q
  ext x
  change
    (∀ Q : Set S, (B.toStructure.weakInduce S).IsClosed Q →
      T ⊆ Q → x ∈ Q) ↔
    (∀ Q : Set S,
      IsUSubstructure (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) Q →
      T ⊆ Q → x ∈ Q)
  constructor
  · intro hx Q hQ hTQ
    exact hx Q ((hClosedEquiv Q).mpr hQ) hTQ
  · intro hx Q hQ hTQ
    exact hx Q ((hClosedEquiv Q).mp hQ) hTQ

/-- Intrinsic minimum exact WEAK generator rank is literally
the published 2019 USize of the induced AMBIENT complete-root
tagged singleton structure on the same weak source subset S.

This does not identify USize of the ambient closed HULL with
USize of the original nonclosed weak test. -/
theorem System.weakGeneratedByAtMost_iff_outputTaggedUSize_le
    (B : System L P V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V)
    [Fintype S] (n : ℕ) :
    (B.toStructure.weakInduce S).GeneratedByAtMost n ↔
      USize (L.outputPartIndexed P).patternClosureRules
        ((patternTagExpansion
          (B.splitOutputParts).toStructure.patternGraph).induce S) ≤ n := by
  let Weak := B.toStructure.weakInduce S
  let Tagged := (patternTagExpansion
    (B.splitOutputParts).toStructure.patternGraph).induce S
  let rules := (L.outputPartIndexed P).patternClosureRules
  have hGen (T : Set S) :
      Weak.GeneratedBy T ↔ IsUGenerating rules Tagged T := by
    change Weak.functionClosure T = Set.univ ↔
      UClosureHull rules Tagged T = Set.univ
    rw [B.weakFunctionClosure_eq_outputTaggedUClosureHull hPos S T]
  constructor
  · rintro ⟨G, hG, hGenerate⟩
    have hU : IsUGenerating rules Tagged (↑G : Set S) :=
      (hGen (↑G : Set S)).mp hGenerate
    exact (USize_le_of_generating rules Tagged G hU).trans hG
  · intro h
    obtain ⟨G, hCard, hU⟩ := USize_spec rules Tagged
    have hBound : G.card ≤ n := by
      rw [hCard]
      exact h
    exact ⟨G, hBound, (hGen (↑G : Set S)).mpr hU⟩

end StructuralRamsey.FunctionalPartite

