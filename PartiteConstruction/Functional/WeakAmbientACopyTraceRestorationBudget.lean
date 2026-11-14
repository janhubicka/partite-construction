import PartiteConstruction.Functional.WeakHistoryFreeTreeBasePower
import PartiteConstruction.Functional.WeakWitnessRestriction
import PartiteConstruction.Iterated.ProjectedPartialRestoration

/-!
# Track D: restore all native functional ambient-A traces at a uniform rank cost

English proof and adversarial NONCIRCULARITY audit committed FIRST:
docs/track-d-english-native-functional-weak-trace-restoration-budget-20261114.md

This is the genuine SET-VALUED FUNCTION analogue of the verified
relational labeled trace-saturation theorem
`RelStructure.LocallyTreeCompletable.toProjectedPartial_identity`.

A weak bare strict functional B-tree witness on an auxiliary LARGER
exact test can be restricted to the original literal weak S while
remembering all genuine ambient full A-copy target marks, by
choosing one representative per EXACT labeled A-trace on S.

This makes the ambient-copy protection a quantitative finite-type
condition, but DOES NOT solve the native n-pass Hales--Jewett
rank induction: the necessary larger bare rank bound must be
supplied independently. No new source closure vertices are
charged to the ORIGINAL tested rank n.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB W P : Type v}

/-- Bare local STRICT full-functional Base-tree property on every
literal finite weak vertex subset of size at most n.

Only the genuinely ambient-relative weak HE is asserted:
complete source-defined fibres when wholly retained and full
embeddings on intrinsic ambient irreducible pieces that lie
entirely inside the weak tested subset. No ambient partial
A-trace marks, projected history or target part labelling. -/
def AtMostBare
    (Base : Structure L VB) (C : Structure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (Target : Structure L Y),
      TreeAmalgam Base Y Target ∧
      ∃ f : (↑S : Set W) → Y,
        IsAmbientRelativeWeakHE C (↑S : Set W) Target f

/-- The genuine native functional exact A-trace saturation theorem.

A uniform bare strict functional B-tree bound at
  n + (n+1)^|A| * |A|
gives a strict history-free target witness on EVERY exact
n-vertex weak S, including a FULL A-copy target embedding
for EVERY actual ambient full irreducible A-copy meeting S.

The auxiliary enlarged set J is ONLY used to request the
existing bare witness; the conclusion is on the ORIGINAL S.
No weak test is closed or replaced by a generated hull, and
no source-undefined function fibre is reflected. -/
theorem AtMostBare.restore_full_ambient_A_traces
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} [Fintype UA] [Fintype W]
    (hA : A.Irreducible)
    (n : ℕ)
    (hC : AtMostBare Base C
      (StructuralRamsey.RelStructure.projectedPartialRestorationBudget
        (U := UA) n))
    (part : W → P) :
    AtMostNoHistory A Base C part n := by
  classical
  intro S hS

  let Test := ↥(↑S : Set W)
  let Copies := Embedding A C
  letI : Fintype Copies := Fintype.ofFinite _
  let trace : Copies → UA → Option Test := fun beta a =>
    if ha : beta a ∈ S then some ⟨beta a, ha⟩ else none

  obtain ⟨J, _hEmpty, hJcard, hrep⟩ :=
    StructuralRamsey.FiniteTrace.selectIndices
      (A := UA) (I := Copies) (T := Test) (X := Copies)
      id trace ∅

  let pairs : Finset (Copies × UA) := J ×ˢ Finset.univ
  let added : Finset W := pairs.image (fun z => z.1 z.2)
  let R : Finset W := S ∪ added

  have hJcard' :
      J.card ≤ (S.card + 1) ^ Fintype.card UA := by
    simpa [Test] using hJcard

  have hAddedCard :
      added.card ≤ J.card * Fintype.card UA := by
    calc
      added.card ≤ pairs.card := Finset.card_image_le
      _ = J.card * (Finset.univ : Finset UA).card := by
        simp [pairs]
      _ = J.card * Fintype.card UA := by simp

  have hRcard :
      R.card ≤
        StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := UA) n := by
    calc
      R.card ≤ S.card + added.card := Finset.card_union_le _ _
      _ ≤ S.card + J.card * Fintype.card UA :=
        Nat.add_le_add_left hAddedCard S.card
      _ ≤ n + ((S.card + 1) ^ Fintype.card UA) *
          Fintype.card UA := by
        apply Nat.add_le_add hS
        exact Nat.mul_le_mul_right _ hJcard'
      _ ≤ n + ((n + 1) ^ Fintype.card UA) *
          Fintype.card UA := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) _
      _ =
        StructuralRamsey.RelStructure.projectedPartialRestorationBudget
          (U := UA) n := rfl

  obtain ⟨Y, Target, hTree, g, hg⟩ := hC R hRcard
  have hSsubR : (↑S : Set W) ⊆ (↑R : Set W) := by
    intro w hw
    exact Finset.mem_union_left _ hw

  let f : Test → Y :=
    g ∘ weakSubsetMap (↑S : Set W) (↑R : Set W) hSsubR
  have hf : IsAmbientRelativeWeakHE C (↑S : Set W)
      Target f := by
    exact hg.restrict_subset (↑S : Set W) hSsubR

  have hCopies : SetAmbientACopyIntersections A C Target
      (↑S : Set W) f := by
    intro beta
    obtain ⟨betaRep, hbetaRepJ, htrace⟩ := hrep beta
    have hbetaRepJ' : betaRep ∈ J := by
      simpa using hbetaRepJ
    have hRepR (a : UA) : betaRep a ∈ R := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(betaRep, a), ?_, rfl⟩
      exact Finset.mem_product.mpr
        ⟨hbetaRepJ', Finset.mem_univ a⟩
    obtain ⟨betaT, hbetaT⟩ := hg.2 A hA betaRep hRepR
    have hRepEq (a : UA) (ha : beta a ∈ S) :
        betaRep a = beta a := by
      have ht := congrFun htrace a
      by_cases hrepS : betaRep a ∈ S
      · simp only [trace, dif_pos hrepS, dif_pos ha] at ht
        exact congrArg Subtype.val (Option.some.inj ht)
      · simp only [trace, dif_neg hrepS, dif_pos ha] at ht
        cases ht
    have hContained : betaT.ContainedInIrreducible := by
      refine ⟨UA, A, hA, betaT, ?_⟩
      intro a
      exact ⟨a, rfl⟩
    refine ⟨betaT, hContained, ?_⟩
    intro a ha
    calc
      betaT a = g ⟨betaRep a, hRepR a⟩ := hbetaT a
      _ = f ⟨beta a, ha⟩ := by
        change g ⟨betaRep a, hRepR a⟩ =
          g ((weakSubsetMap (↑S : Set W) (↑R : Set W)
            hSsubR) ⟨beta a, ha⟩)
        apply congrArg g
        apply Subtype.ext
        exact hRepEq a ha

  have hHistory : SetRespectsProjectedHistory
      part (↑S : Set W) f [] := by
    intro K hK
    cases hK
  exact ⟨Y, Target, hTree, f, hf, hCopies, hHistory⟩

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
