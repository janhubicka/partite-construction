import PartiteConstruction.Functional.EHNClosedPullbackRootDichotomy
import PartiteConstruction.Functional.EHNDefectMinimumTwoInputs
import PartiteConstruction.Functional.EHNNonFullCrossChartTrichotomy

/-!
# Track D: original-source defects on the actual native closed-test separator

The common separator in an ACTUAL native one-copy EHN binary attachment
inherits the CANONICAL EHN label map into its selected A. Its failure to
be a FULL root embedding has exactly three original-source causes:
two genuinely distinct source vertices have the same label, or some
actual OLD relation/function input tuple with TWO DISTINCT source input
vertices is not reflected.

This specializes the checked source defect theorem to the actual
`closedTestPullback` geometry. Neither the exact weak tested set nor
the root's generating set is replaced by a function-closed hull.

In the subcase where ALL primitive old function/relation arities are
at most one, the canonical root map is a FULL embedding precisely
when its vertex map is injective: no other root defect can occur.
A full root embedding still does NOT automatically yield an incoming
old-copy strict relative B-tree extension over the same Start.

The attachment is an actual full native UnitAttachD, with generic control
and support map; this DOES NOT certify the full ordered HJ line history.
The numbered survey Appendix A is frozen and untouched.
-/

namespace StructuralRamsey.FunctionalPartite.Attachment

open StructuralRamsey.Structure
universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- Exhaustive ORIGINAL-SOURCE trichotomy for the actual full common
separator of a genuine native functional one-copy attachment.
The two tuple failure alternatives each preserve a real named
primitive input and two DISTINCT original source input vertices.

No global source finiteness, root-label injectivity, total-fibre
homomorphism, or exact weak test size enlargement is assumed.

This is still a source-side classification, not a target B-tree
relative completion theorem. -/
theorem closedTestPullback_common_fullOrCollisionOrMultiInputDefect
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (alpha : Structure.Embedding A Douter)
    (Dsys : System L P W)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)) Dsys)
    (Test : Set
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.IsClosed Test) :
    let Supp := B.support alpha.toFunctionEmbedding
    let hSupp := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
    let q : pb.Common → U :=
      (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
    (∃ e : Structure.Embedding pb.common A, ∀ x, e x = q x) ∨
      (∃ x y : pb.Common, x ≠ y ∧ q x = q y) ∨
      (∃ (R : L.RelSymbol)
        (xs : Fin (L.relArity R) → pb.Common)
        (i j : Fin (L.relArity R)),
          xs i ≠ xs j ∧
          A.rel R (q ∘ xs) ∧ ¬ pb.common.rel R xs) ∨
      (∃ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → pb.Common)
        (i j : Fin (L.funcArity F)),
          xs i ≠ xs j ∧
          (A.func F (q ∘ xs)).Nonempty ∧
          ¬ (pb.common.func F xs).Nonempty) := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let q : pb.Common → U :=
    (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
  have hp : pb.common.IsEHNHomomorphismEmbedding A q :=
    closedTestPullback_common_EHN
      B Douter hB A alpha Dsys f Test hTest
  by_cases hFull : ∃ e : Structure.Embedding pb.common A, ∀ x, e x = q x
  · exact Or.inl hFull
  · rcases hp.nonFull_exactThreeDefects hFull with
      ⟨x, y, hDistinct, hEq⟩ |
      ⟨R, xs, hTarget, hSource⟩ |
      ⟨F, xs, hTarget, hSource⟩
    · exact Or.inr (Or.inl ⟨x, y, hDistinct, hEq⟩)
    · obtain ⟨i, j, hDistinct⟩ :=
        hp.relationFailure_hasTwoDistinctInputs
          R xs hTarget hSource
      exact Or.inr (Or.inr
        (Or.inl ⟨R, xs, i, j, hDistinct, hTarget, hSource⟩))
    · obtain ⟨i, j, hDistinct⟩ :=
        hp.domainFailure_hasTwoDistinctInputs
          F xs hTarget hSource
      exact Or.inr (Or.inr
        (Or.inr ⟨F, xs, i, j, hDistinct, hTarget, hSource⟩))

/-- With only unary/nullary OLD primitive inputs, the ACTUAL closed
native separator's canonical EHN projection is FULL precisely if its
vertex map is injective. In arbitrary arity this equivalence fails:
extra target relations and source-undefined target-defined function
tuples with two original source inputs can remain. -/
theorem closedTestPullback_common_full_iff_injective_of_arities_le_one
    (B : System L P V) (Douter : Structure L P)
    (hB : B.WeaklyPartiteOver Douter)
    (A : Structure L U) (alpha : Structure.Embedding A Douter)
    (Dsys : System L P W)
    (f : FunctionalPartite.Embedding
      (B.induce (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)) Dsys)
    (Test : Set
      (Structure.Attachment.Vertex
        (B.support alpha.toFunctionEmbedding)
        (W := W) (I := PUnit.{v+1})))
    (hTest :
      (UnitAttachD B (B.support alpha.toFunctionEmbedding)
        (B.weak_support_closed Douter hB.1 A alpha)
        Dsys f).toStructure.IsClosed Test)
    (hRelArity : ∀ R, L.relArity R ≤ 1)
    (hFuncArity : ∀ F, L.funcArity F ≤ 1) :
    let Supp := B.support alpha.toFunctionEmbedding
    let hSupp := B.weak_support_closed Douter hB.1 A alpha
    let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
    let q : pb.Common → U :=
      (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
    (∃ e : Structure.Embedding pb.common A, ∀ x, e x = q x) ↔
      Function.Injective q := by
  let Supp := B.support alpha.toFunctionEmbedding
  let hSupp := B.weak_support_closed Douter hB.1 A alpha
  let pb := closedTestPullback B Supp hSupp Dsys f Test hTest
  let q : pb.Common → U :=
    (B.weakRestrict Douter hB.1 A alpha).part ∘ pb.commonMap
  have hp : pb.common.IsEHNHomomorphismEmbedding A q :=
    closedTestPullback_common_EHN
      B Douter hB A alpha Dsys f Test hTest
  constructor
  · rintro ⟨e, he⟩ x y hxy
    apply e.injective
    calc
      e x = q x := he x
      _ = q y := hxy
      _ = e y := (he y).symm
  · intro hInjective
    exact hp.fullEmbedding_of_allArity_le_one
      hInjective hRelArity hFuncArity

end StructuralRamsey.FunctionalPartite.Attachment
