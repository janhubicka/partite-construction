import PartiteConstruction.Ramsey.ClosureProjectedGenerators
import PartiteConstruction.Ramsey.ClosureProjectedCompletion

/-! # Mixed gluing from one ambient projection and two support budgets

The previous mixed-completion theorem asked for a shared closed K-member
Q and its embeddings into both projected sources. Here Q, both sources,
all three maps and their compatibility are constructed from ONE ambient
projection. The raw separator image need only lie in a closed A-copy.

The projected-side sources are the closed hulls of finite vertex supports
JL and JR. Their U-size bounds follow from |JL|,|JR| <= j. The required
independent K-completions follow from the prior rank-j invariant.

The geometric support-containment hypotheses remain explicit; the theorem
does not assert that every Picture cut supplies the two budgets. The
second theorem obtains those containments from actual side generators.
This module uses the working closed-test convention, not a redefinition
of the literal 2019 completion or local-finiteness predicates.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- One projection supplies the SAME boundary closure in both projected
sides. Rank control on the closed ambient structure then completes the
free source amalgam, provided both side images have small generating
supports and the projected separator lies in a closed A-copy in K. -/
theorem HasClosedUKCompletion.of_common_projection_supports
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {F : RelStructure L Y},
      K F → IsUClosed rules E → Embedding E F → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    {UA H E F C V : Type v}
    {A : RelStructure L UA} {D : RelStructure L V}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite V] [DecidableEq V]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left) (hRight : IsUSemiClosed rules Right)
    (hKA : K A) (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D) (p : C → V)
    (hp : IsClosedUHomomorphismEmbedding rules Whole D p)
    (hSeparator : ∀ r : H, p (iL (sL r)) ∈ Set.range a)
    (JL JR : Finset V) (j : ℕ)
    (hJL : JL.card ≤ j) (hJR : JR.card ≤ j)
    (hRangeL : ∀ x : E, p (iL x) ∈ UClosureHull rules D (↑JL : Set V))
    (hRangeR : ∀ x : F, p (iR x) ∈ UClosureHull rules D (↑JR : Set V))
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules Whole := by
  classical
  let TL : Set V := UClosureHull rules D (↑JL : Set V)
  let TR : Set V := UClosureHull rules D (↑JR : Set V)
  let b : H → V := fun r => p (iL (sL r))
  let TQ : Set V := UClosureHull rules D (Set.range b)
  letI : Fintype TL := Fintype.ofFinite TL
  letI : Fintype TR := Fintype.ofFinite TR
  have hBoth (r : H) : p (iL (sL r)) = p (iR (sR r)) :=
    congrArg p ((hSrc.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩)
  have hSep : Set.range b ⊆ Set.range a := by
    rintro x ⟨r, rfl⟩
    exact hSeparator r
  obtain ⟨hQK, _⟩ := closedHull_in_class_of_subset_copy
    K rules hHereditary hKIrr hKA hA hD a (Set.range b) hSep
  have hQClosed : IsUClosed rules (D.induce TQ) :=
    hD.induce_UClosureHull (Set.range b)
  have hQL : TQ ⊆ TL := by
    apply UClosureHull_minimal rules D
      (UClosureHull_isUSubstructure rules D (↑JL : Set V))
    rintro x ⟨r, rfl⟩
    exact hRangeL (sL r)
  have hQR : TQ ⊆ TR := by
    apply UClosureHull_minimal rules D
      (UClosureHull_isUSubstructure rules D (↑JR : Set V))
    rintro x ⟨r, rfl⟩
    change p (iL (sL r)) ∈ TR
    rw [hBoth r]
    exact hRangeR (sR r)
  let q : H → TQ := fun r =>
    ⟨b r, subset_UClosureHull rules D (Set.range b) ⟨r, rfl⟩⟩
  let rL : Embedding (D.induce TQ) (D.induce TL) := {
    toFun := fun x => ⟨x.1, hQL x.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : TL => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let rR : Embedding (D.induce TQ) (D.induce TR) := {
    toFun := fun x => ⟨x.1, hQR x.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : TR => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let pL : E → TL := fun x => ⟨p (iL x), hRangeL x⟩
  let pR : F → TR := fun x => ⟨p (iR x), hRangeR x⟩
  have hpL : IsClosedUHomomorphismEmbedding rules Left (D.induce TL) pL :=
    (hp.precomp_embedding iL).codRestrict TL hRangeL
  have hpR : IsClosedUHomomorphismEmbedding rules Right (D.induce TR) pR :=
    (hp.precomp_embedding iR).codRestrict TR hRangeR
  have hRootL : ∀ r, pL (sL r) = rL (q r) := fun _ => Subtype.ext rfl
  have hRootR : ∀ r, pR (sR r) = rR (q r) :=
    fun r => Subtype.ext (hBoth r).symm
  have hDL : HasClosedUKCompletion K rules (D.induce TL) :=
    hRank TL (hD.induce_UClosureHull (↑JL : Set V))
      ((USize_induce_UClosureHull_le rules D JL).trans hJL)
  have hDR : HasClosedUKCompletion K rules (D.induce TR) :=
    hRank TR (hD.induce_UClosureHull (↑JR : Set V))
      ((USize_induce_UClosureHull_le rules D JR).trans hJR)
  exact HasClosedUKCompletion.of_independent_projected_completions
    rules hK hKIrr hSrc hRoot hLeft hRight
    (D.induce TQ) hQK hQClosed (D.induce TL) (D.induce TR)
    pL pR hpL hpR q rL rR hRootL hRootR hDL hDR

/-- The support-containment premises above follow from side generators
and relation preservation. Only the two projected cardinal budgets and
the actual free-source geometry remain inputs. Neither projected image
is required to be U-closed, and the separator hull is built automatically. -/
theorem HasClosedUKCompletion.of_common_projection_generators
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {F : RelStructure L Y},
      K F → IsUClosed rules E → Embedding E F → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    {UA H E F C V : Type v}
    {A : RelStructure L UA} {D : RelStructure L V}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite V] [DecidableEq V]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left) (hRight : IsUSemiClosed rules Right)
    (hKA : K A) (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D) (p : C → V)
    (hp : IsClosedUHomomorphismEmbedding rules Whole D p)
    (hSeparator : ∀ r : H, p (iL (sL r)) ∈ Set.range a)
    (GLeft : Finset E) (GRight : Finset F)
    (hGL : IsUGenerating rules Left (↑GLeft : Set E))
    (hGR : IsUGenerating rules Right (↑GRight : Set F))
    (j : ℕ)
    (hBudgetL : (GLeft.image (p ∘ iL)).card ≤ j)
    (hBudgetR : (GRight.image (p ∘ iR)).card ≤ j)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules Whole := by
  have hRangeL (x : E) : p (iL x) ∈
      UClosureHull rules D (↑(GLeft.image (p ∘ iL)) : Set V) := by
    simpa only [Finset.coe_image, Function.comp_apply] using
      (hp.precomp_embedding iL).1.range_subset_generatedHull
        (↑GLeft : Set E) hGL ⟨x, rfl⟩
  have hRangeR (x : F) : p (iR x) ∈
      UClosureHull rules D (↑(GRight.image (p ∘ iR)) : Set V) := by
    simpa only [Finset.coe_image, Function.comp_apply] using
      (hp.precomp_embedding iR).1.range_subset_generatedHull
        (↑GRight : Set F) hGR ⟨x, rfl⟩
  exact HasClosedUKCompletion.of_common_projection_supports
    rules hK hHereditary hKIrr hSrc hRoot hLeft hRight hKA hA hD
    a p hp hSeparator (GLeft.image (p ∘ iL)) (GRight.image (p ∘ iR))
    j hBudgetL hBudgetR hRangeL hRangeR hRank

end StructuralRamsey.RelStructure
