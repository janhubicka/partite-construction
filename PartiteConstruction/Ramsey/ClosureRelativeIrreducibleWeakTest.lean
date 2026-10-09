import PartiteConstruction.Iterated.WeakFreeAmalgamInduce
import PartiteConstruction.Ramsey.ClosureRelativeSideRange
import PartiteConstruction.Ramsey.ClosureUIrreducible2019

/-! # Relative U-irreducibility of arbitrary weak vertex tests

A "relative" U-irreducible structure cannot be freely decomposed into
two proper *U-substructures of itself* (Definition 2.22).  For
non-U-closed weak tests, this differs from demanding that each side be
an intrinsically U-closed structure.  The distinction is kept explicit:
the existing `IsUIrreducible` predicate is NOT silently redefined here.

The payoff is an exact weak side-localization theorem.  In a free
amalgam of U-semi-closed structures over a U-closed common root, a
relative U-irreducible induced test on ANY vertex set stays on one side.
Neither the test nor the induced common root must be U-closed.

Before identifying this predicate with the printed 2019 U-irreducibility
notion, the source's "U-closed substructure" terminology must be
reconciled with its later Definition 2.22.  This module proves the
mathematical relative statement without making that editorial decision.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {U V H E F C : Type v}

/-- Indecomposability over *relative* U-substructures of the given
ambient structure, rather than over intrinsically U-closed structures. -/
def IsURelativelyIrreducible
    (rules : ClosureDescription L) (A : RelStructure L U) : Prop :=
  ∀ {H E F : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left A} {iR : Embedding Right A},
    IsFreeAmalgam sL sR iL iR →
    IsUSubstructure rules A (Set.range iL) →
    IsUSubstructure rules A (Set.range iR) →
    Function.Surjective iL ∨ Function.Surjective iR

/-- An ordinary irreducible relational structure is indecomposable
even with relative U-closure restrictions. -/
theorem Irreducible.isURelativelyIrreducible
    {A : RelStructure L U}
    (hA : A.Irreducible) (rules : ClosureDescription L) :
    IsURelativelyIrreducible rules A := by
  intro H E F Root Left Right sL sR iL iR hFree _ _
  have hTest :
      (A.induce (Set.range (Embedding.id A))).Irreducible :=
    hA.range_embedding (Embedding.id A)
  rcases hFree.irreducible_side
      (Set.range (Embedding.id A)) hTest with hLeft | hRight
  · left
    intro a
    obtain ⟨b, hb⟩ := hLeft ⟨a, ⟨a, rfl⟩⟩
    exact ⟨b, hb.symm⟩
  · right
    intro a
    obtain ⟨b, hb⟩ := hRight ⟨a, ⟨a, rfl⟩⟩
    exact ⟨b, hb.symm⟩

/-- Exact weak induction of a relative U-substructure image along a
full embedding.  The induced set S can omit closure outputs. -/
theorem IsUSubstructure.weakInduce_embeddingRange
    {A : RelStructure L U} {B : RelStructure L V}
    {rules : ClosureDescription L}
    (e : Embedding A B)
    (hRange : IsUSubstructure rules B (Set.range e))
    (S : Set V)
    (j : Embedding (A.induce (e ⁻¹' S)) (B.induce S))
    (hj : ∀ a : (e ⁻¹' S), (j a).1 = e a.1) :
    IsUSubstructure rules (B.induce S) (Set.range j) := by
  intro rule hrule t ht hRoot jidx
  have htB : B.rel rule.symbol (Subtype.val ∘ t) := ht
  have hRootRange :
      ∀ k : Fin rule.rootSize,
        (Subtype.val ∘ t) (k.castLE rule.rootLE) ∈ Set.range e := by
    intro k
    obtain ⟨a, ha⟩ := hRoot k
    refine ⟨a.1, ?_⟩
    calc
      e a.1 = (j a).1 := (hj a).symm
      _ = (t (k.castLE rule.rootLE)).1 :=
        congrArg Subtype.val ha
  obtain ⟨a, ha⟩ :=
    hRange rule hrule (Subtype.val ∘ t) htB hRootRange jidx
  have haS : e a ∈ S := by
    rw [ha]
    exact (t jidx).2
  let aS : e ⁻¹' S := ⟨a, haS⟩
  refine ⟨aS, ?_⟩
  apply Subtype.ext
  calc
    (j aS).1 = e a := hj aS
    _ = (t jidx).1 := ha

variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Relative U-irreducible weak tests in a free amalgam of U-semi-closed
sides over a U-closed common root must lie entirely on one side.
The test S is arbitrary: it need not be U-closed or a U-substructure. -/
theorem IsFreeAmalgam.uRelativeIrreducible_weak_side
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (S : Set C)
    (hIrred :
      IsURelativelyIrreducible rules (Whole.induce S)) :
    (∀ z : S, ∃ a : E, z.1 = iL a) ∨
    (∀ z : S, ∃ b : F, z.1 = iR b) := by
  classical
  let Lset : Set E := iL ⁻¹' S
  let Rset : Set F := iR ⁻¹' S
  have hWholeLeft : IsUSubstructure rules Whole (Set.range iL) :=
    hFree.left_range_isUSubstructure hRoot hRight
  have hWholeRight : IsUSubstructure rules Whole (Set.range iR) :=
    hFree.right_range_isUSubstructure hRoot hLeft
  obtain ⟨mL, mR, jL, jR, hRestricted, hjL, hjR⟩ :=
    hFree.weakInduce_withMaps S
  have hSmallLeft :
      IsUSubstructure rules (Whole.induce S) (Set.range jL) :=
    IsUSubstructure.weakInduce_embeddingRange
      iL hWholeLeft S jL hjL
  have hSmallRight :
      IsUSubstructure rules (Whole.induce S) (Set.range jR) :=
    IsUSubstructure.weakInduce_embeddingRange
      iR hWholeRight S jR hjR
  rcases hIrred hRestricted hSmallLeft hSmallRight with
      hSurjL | hSurjR
  · left
    intro z
    obtain ⟨a, ha⟩ := hSurjL z
    exact ⟨a.1, (congrArg Subtype.val ha).symm.trans (hjL a)⟩
  · right
    intro z
    obtain ⟨b, hb⟩ := hSurjR z
    exact ⟨b.1, (congrArg Subtype.val hb).symm.trans (hjR b)⟩

/-- Contrapositive form: a weak vertex test meeting both exclusive
sides cannot be relatively U-irreducible. -/
theorem IsFreeAmalgam.mixed_weak_not_uRelativeIrreducible
    (hFree : IsFreeAmalgam sL sR iL iR)
    {rules : ClosureDescription L}
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (S : Set C)
    (zLeft : S) (hzLeft : ¬ ∃ a : E, zLeft.1 = iL a)
    (zRight : S) (hzRight : ¬ ∃ b : F, zRight.1 = iR b) :
    ¬ IsURelativelyIrreducible rules (Whole.induce S) := by
  intro hIrred
  rcases hFree.uRelativeIrreducible_weak_side
      hRoot hLeft hRight S hIrred with hOnLeft | hOnRight
  · exact hzLeft (hOnLeft zLeft)
  · exact hzRight (hOnRight zRight)

end StructuralRamsey.RelStructure
