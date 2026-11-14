import PartiteConstruction.Functional.TrackAArbitraryClippedWeakImagePositive2019
import PartiteConstruction.Functional.PartialClippedWeakImageSaturationCounterexample2019

/-!
# Track A: minimal active-fibre cover for exact clipped weak image maps

Fix an original source-defined partial homomorphism f : A → B and an
ARBITRARY literal source vertex subset S. A weak input tuple in S
with ambient complete defined value Q is still weak-defined whenever
Q is genuinely empty or Q meets S.

If Q meets S, the source clips Q to Q∩S, while the target clips the
mapped complete value f[Q] to f[Q]∩f[S]. Equality of the two projected
weak fibres is therefore precisely the local active-fibre condition

    f[Q∩S] = f[Q]∩f[S].

The inclusion from left to right always holds. The converse amounts
to each target output label that survives in the projected test being
represented by an output vertex of this SAME active source fibre that
survives in S. This can hold without S being fibre-saturated, and it
is strictly weaker than global part saturation.

The condition is imposed only when Q∩S is nonempty; if the ambient
value Q is defined-empty, both weak values remain defined-empty and
have no output incidences. Undefined/lost source applications impose
no target-fibre equation under original 2019 partial semantics.

This is a source-map criterion, not an arbitrary U-closed local-class
completion or strict history-compatible functional B-tree theorem.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- The minimal local output-cover condition for a weak test S:
over each ambient function input whose nonempty output survives in S,
every target output label both belonging to the original complete
source output and appearing in the exact projected vertex carrier
has a representative in the surviving SAME source output fibre. -/
def ActiveProjectedFibreCover
    (A : PartialSetStructure L V) (f : V → W) (S : Set V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (Q : Set V), A.func F (Subtype.val ∘ xs) = some Q →
    (Q ∩ S).Nonempty →
    ∀ y : V, y ∈ Q → f y ∈ f '' S →
      ∃ z : V, z ∈ Q ∧ z ∈ S ∧ f z = f y

/-- For any original source-defined map, local active-fibre cover is
EXACTLY the no-extra-output condition on the two clipped weak
structures. No closure hull, saturation, injectivity, or domain
reflection is assumed. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_noExtra_iff_activeCover
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) (S : Set V) :
    NoExtraTargetOutputsOnDefined
        (A.weakInduce S) (B.weakInduce (f '' S))
        (clippedWeakImageMap f S) ↔
      ActiveProjectedFibreCover A f S := by
  classical
  constructor
  · intro hNo F xs Q hQ hMeet a ha haT
    let U : Set S := {z : S | z.1 ∈ Q}
    have hQNonempty : Q.Nonempty := by
      obtain ⟨z, hz, _⟩ := hMeet
      exact ⟨z, hz⟩
    have hWeak : (A.weakInduce S).func F xs = some U := by
      change weakValue S (A.func F (Subtype.val ∘ xs)) = some U
      rw [hQ]
      simp [weakValue, hQNonempty, hMeet, U]
    have hB : B.func F (f ∘ (Subtype.val ∘ xs)) =
        some (Structure.imageSet f Q) :=
      hf.2 F (Subtype.val ∘ xs) Q hQ
    let gy : f '' S := ⟨f a, haT⟩
    have hTarget : (B.weakInduce (f '' S)).HasOutput F
        (clippedWeakImageMap f S ∘ xs) gy := by
      change ∃ Z : Set (f '' S),
        weakValue (f '' S)
          (B.func F (f ∘ (Subtype.val ∘ xs))) = some Z ∧ gy ∈ Z
      apply (weakValue_hasOutput_iff (f '' S)
        (B.func F (f ∘ (Subtype.val ∘ xs))) gy).mpr
      exact ⟨Structure.imageSet f Q, hB, ⟨a, ha, rfl⟩⟩
    have hIn : gy ∈ Structure.imageSet (clippedWeakImageMap f S) U :=
      hNo F xs U hWeak gy hTarget
    obtain ⟨z, hzU, hEq⟩ := hIn
    exact ⟨z.1, hzU, z.2, congrArg Subtype.val hEq⟩
  · intro hCover F xs U hWeak y hTarget
    change weakValue S (A.func F (Subtype.val ∘ xs)) = some U at hWeak
    have hDef : (A.weakInduce S).Defined F xs := ⟨U, hWeak⟩
    obtain ⟨Q, hQ, hSurvive⟩ :=
      (weakInduce_defined_iff_exact A S F xs).mp hDef
    have hB : B.func F (f ∘ (Subtype.val ∘ xs)) =
        some (Structure.imageSet f Q) :=
      hf.2 F (Subtype.val ∘ xs) Q hQ
    change ∃ Z : Set (f '' S),
      weakValue (f '' S)
        (B.func F (f ∘ (Subtype.val ∘ xs))) = some Z ∧ y ∈ Z
      at hTarget
    obtain ⟨T, hT, hyT⟩ :=
      (weakValue_hasOutput_iff (f '' S)
        (B.func F (f ∘ (Subtype.val ∘ xs))) y).mp hTarget
    have hTEq : T = Structure.imageSet f Q :=
      Option.some.inj (hT.symm.trans hB)
    have hyImage : y.1 ∈ Structure.imageSet f Q := by
      simpa only [hTEq] using hyT
    obtain ⟨a, haQ, haY⟩ := hyImage
    have hMeet : (Q ∩ S).Nonempty := by
      rcases hSurvive with hEmpty | hMeet
      · subst Q
        simp at haQ
      · exact hMeet
    have haT : f a ∈ f '' S := by
      rw [haY]
      exact y.2
    obtain ⟨z, hzQ, hzS, hzF⟩ :=
      hCover F xs Q hQ hMeet a haQ haT
    have hWeakOutput :
        ∃ U' : Set S,
          weakValue S (A.func F (Subtype.val ∘ xs)) = some U' ∧
            (⟨z, hzS⟩ : S) ∈ U' :=
      (weakValue_hasOutput_iff S
        (A.func F (Subtype.val ∘ xs)) (⟨z, hzS⟩ : S)).mpr
        ⟨Q, hQ, hzQ⟩
    obtain ⟨U', hU', hzU'⟩ := hWeakOutput
    have hUEq : U' = U :=
      Option.some.inj (hU'.symm.trans hWeak)
    refine ⟨(⟨z, hzS⟩ : S), ?_, ?_⟩
    · simpa only [hUEq] using hzU'
    · apply Subtype.ext
      exact hzF.trans haY

/-- Direct useful form for the projection step: the clipped weak map
is an exact ORIGINAL partial-function homomorphism precisely when
active source output fibres cover all target output labels still
present in the literal projected carrier. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_originalPartial_iff_activeCover
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f) (S : Set V) :
    IsOriginalPartialHomomorphism
        (A.weakInduce S) (B.weakInduce (f '' S))
        (clippedWeakImageMap f S) ↔
      ActiveProjectedFibreCover A f S := by
  exact (hf.clippedWeakImage_originalPartial_iff_noExtra S).trans
    (hf.clippedWeakImage_noExtra_iff_activeCover S)

/-- Global fibre saturation is sufficient for active fibre cover,
but the latter only asks for witnesses inside each currently active
function value. -/
theorem ActiveProjectedFibreCover.of_saturated
    (A : PartialSetStructure L V) (f : V → W) (S : Set V)
    (hSat : ∀ x : V, f x ∈ f '' S → x ∈ S) :
    ActiveProjectedFibreCover A f S := by
  intro F xs Q hQ hMeet y hy hTarget
  exact ⟨y, hy, hSat y hTarget, rfl⟩

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

/-- A nonvacuous test with TWO active distinct output labels, using the
same nonsaturated three-to-two projection as the counterexample to
unrestricted weak exactness. This time the entire source function
value is contained in the weak carrier. -/
def coveredSource : PartialSetStructure exampleLanguage (Fin 3) where
  rel := fun R => Empty.elim R
  func := fun _ _ => some support

def coveredTarget : PartialSetStructure exampleLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ _ => some (Structure.imageSet projection support)

/-- The original complete function fibre maps ONTO its target value. -/
theorem coveredOriginalPartial :
    IsOriginalPartialHomomorphism coveredSource coveredTarget projection := by
  constructor
  · intro R
    exact Empty.elim R
  · intro F xs U hU
    have hEq : support = U := Option.some.inj hU
    subst U
    rfl

/-- The active source fibre is wholly contained in the weak carrier.
Thus local output-cover holds even though the support does NOT
contain all source vertices over its occupied projected labels. -/
theorem coveredActiveFibre :
    ActiveProjectedFibreCover coveredSource projection support := by
  intro F xs Q hQ hMeet y hy hTarget
  have hEq : Q = support := by
    have h : some support = some Q := by
      simpa only [coveredSource] using hQ
    exact (Option.some.inj h).symm
  exact ⟨y, hy, by simpa only [hEq] using hy, rfl⟩

/-- Strictness with a genuinely defined, two-output source function:
local active-fibre cover is weaker than global fibre saturation. -/
theorem coveredActiveFibre_not_saturated :
    ActiveProjectedFibreCover coveredSource projection support ∧
      ¬ (∀ x : Fin 3, projection x ∈ projection '' support →
        x ∈ support) := by
  exact ⟨coveredActiveFibre, not_fibreSaturated⟩

/-- The non-saturated example nevertheless has a correct complete
CLIPPED weak-image partial projection by the local theorem. -/
theorem coveredWeakImage_originalPartial :
    IsOriginalPartialHomomorphism
      (coveredSource.weakInduce support)
      (coveredTarget.weakInduce (projection '' support))
      (clippedWeakImageMap projection support) := by
  exact (coveredOriginalPartial.clippedWeakImage_originalPartial_iff_activeCover
    support).mpr coveredActiveFibre

end StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample
