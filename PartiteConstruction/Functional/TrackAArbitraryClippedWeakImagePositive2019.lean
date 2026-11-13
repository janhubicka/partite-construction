import PartiteConstruction.Functional.PartialDomainGraphExactHom2019
import PartiteConstruction.Functional.PartialWeakAmbientDomainGraph2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track A: exact weak-image projections without part saturation — positive versus exact

A source-defined original-2019 partial homomorphism f : A → B may induce
a weak map on ANY literal source vertex subset S, even when S is NOT
saturated under fibres of f. Write T=f[S], with unchanged vertex set
and the canonical restricted map S→T.

On the independent Dom_F / Graph_F RELATIONAL encodings of the two
CLIPPED weak structures, this induced map is ALWAYS a *positive*
homomorphism. In particular a source weak-defined input remains
defined in the target weak image, and every surviving positive output
incidence is preserved. No reflection of undefined inputs or
surjectivity on the target value fibre is claimed.

The exact obstruction to this map being a genuine original-partial
FUNCTION homomorphism is the already verified precise
NoExtraTargetOutputsOnDefined condition on the TWO WEAK STRUCTURES:
there must be no target weak output over a source weak-defined input
that is absent from the image of its surviving source outputs.

This gives the right interface for arbitrary non-saturated weak tests,
without silently strengthening positive OLD maps into exact functional
projections. Fibre saturation is one sufficient condition, but is not
assumed here. All arities, repetitions, defined-empty values, and
genuinely multivalued outputs are allowed.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- The canonical weak projection on EXACT literal source/image sets.
This is the same map as wholeWeakImageMap, but used for CLIPPED
weak restrictions. -/
def clippedWeakImageMap (f : V → W) (S : Set V) : S → f '' S :=
  fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩

/-- A source-defined original partial function map preserves all
POSITIVE relations of the separate domain/output graphs after
CLIPPED weak restriction on an arbitrary source subset and its
literal image. No fibre saturation is needed for this weaker map. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_graphHom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) :
    (domainGraph (A.weakInduce S)).IsHomomorphism
      (domainGraph (B.weakInduce (f '' S)))
      (clippedWeakImageMap f S) := by
  let T : Set W := f '' S
  let g : S → T := clippedWeakImageMap f S
  have hTuple (n : ℕ) (xs : Fin n → S) :
      Subtype.val ∘ (g ∘ xs) = f ∘ (Subtype.val ∘ xs) := by
    funext i
    rfl
  intro symbol xs hSource
  cases symbol with
  | inl R =>
      change B.rel R (Subtype.val ∘ (g ∘ xs))
      rw [hTuple]
      exact hf.1 R (Subtype.val ∘ xs) hSource
  | inr symbol =>
      cases symbol with
      | inl F =>
          change (B.weakInduce T).Defined F (g ∘ xs)
          change (A.weakInduce S).Defined F xs at hSource
          obtain ⟨Q, hQ, hLive⟩ :=
            (weakInduce_defined_iff_exact A S F xs).mp hSource
          have hTarget :
              B.func F (f ∘ (Subtype.val ∘ xs)) =
                some (Structure.imageSet f Q) :=
            hf.2 F (Subtype.val ∘ xs) Q hQ
          apply (weakInduce_defined_iff_exact B T F (g ∘ xs)).mpr
          refine ⟨Structure.imageSet f Q, ?_, ?_⟩
          · change B.func F (Subtype.val ∘ (g ∘ xs)) =
                some (Structure.imageSet f Q)
            rw [hTuple]
            exact hTarget
          · rcases hLive with hEmpty | hMeet
            · left
              subst Q
              simp [Structure.imageSet]
            · right
              obtain ⟨a, haQ, haS⟩ := hMeet
              exact ⟨f a, ⟨a, haQ, rfl⟩, ⟨a, haS, rfl⟩⟩
      | inr F =>
          have hAmbient :
              ((domainGraph A).induce S).rel
                (.inr (.inr F)) xs :=
            (weakInduce_domainGraph_output_iff A S F xs).mp hSource
          change (domainGraph A).rel (.inr (.inr F))
            (Subtype.val ∘ xs) at hAmbient
          have hB : (domainGraph B).rel (.inr (.inr F))
              (f ∘ (Subtype.val ∘ xs)) :=
            hf.to_domainGraph_hom (.inr (.inr F))
              (Subtype.val ∘ xs) hAmbient
          have hTargetAmbient :
              ((domainGraph B).induce T).rel
                (.inr (.inr F)) (g ∘ xs) := by
            change (domainGraph B).rel (.inr (.inr F))
              (Subtype.val ∘ (g ∘ xs))
            rw [hTuple]
            exact hB
          exact (weakInduce_domainGraph_output_iff B T F
            (g ∘ xs)).mpr hTargetAmbient

/-- The sharp extra property needed to promote this ALWAYS-positive
CLIPPED weak-image graph map to a genuine source-defined partial
functional homomorphism. The condition is local to source-defined
weak inputs, and permits arbitrary new target-defined operations on
source-undefined inputs. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_originalPartial_iff_noExtra
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) :
    IsOriginalPartialHomomorphism
        (A.weakInduce S) (B.weakInduce (f '' S))
        (clippedWeakImageMap f S) ↔
      NoExtraTargetOutputsOnDefined
        (A.weakInduce S) (B.weakInduce (f '' S))
        (clippedWeakImageMap f S) := by
  constructor
  · intro h
    exact ((originalPartialHom_iff_domainGraphHom_and_noExtra
      (A.weakInduce S) (B.weakInduce (f '' S))
      (clippedWeakImageMap f S)).mp h).2
  · intro hNoExtra
    exact (originalPartialHom_iff_domainGraphHom_and_noExtra
      (A.weakInduce S) (B.weakInduce (f '' S))
      (clippedWeakImageMap f S)).mpr
        ⟨hf.clippedWeakImage_graphHom S, hNoExtra⟩

end StructuralRamsey.PartialSetStructure
