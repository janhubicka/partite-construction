import PartiteConstruction.Functional.PartialDomainGraphExactHom2019
import PartiteConstruction.Structure.PartialSetFunctionsWeakEmbedding

/-!
# Track A: a genuine multivalued clipped weak image needs fibre saturation

The full source-defined partial map A→B can fail to restrict to a
source-defined map from A|ᵂ_S to B|ᵂ_(f[S]) when S is NOT saturated
under f. This is not a limitation of whole-fibre weak restriction:
the counterexample specifically uses the displayed CLIPPED convention.

Take three source vertices 0,1,2 and two target vertices 0,1.
Let f(0)=0 and f(1)=f(2)=1. Every source unary input has the
defined output set {0,1}; every target unary input has its exact
image {0,1}. Thus f is an honest original-2019 source-defined
partial homomorphism. Choose S={0,2}. Its projected image is
all target vertices, but source vertex 1 is absent despite
f(1)=f(2). The clipped source output retains only {0}, whereas
the target restriction retains {0,1}. Therefore the same
projected map of clipped weak structures is NOT source-defined
partial, even though the original unrestricted map is.

The example isolates why the exact-preimage/fibre-saturation
hypothesis of the positive Track A transfer is mathematically
meaningful for multivalued source functions. It does not alter
the source language, vertex sets or domain conventions and
does not assert any strict B-tree counterexample.
-/

namespace StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

def projection : Fin 3 → Fin 2 :=
  fun x => if x = 0 then 0 else 1

def output : Set (Fin 3) := {(0 : Fin 3), (1 : Fin 3)}

def support : Set (Fin 3) := {(0 : Fin 3), (2 : Fin 3)}

def source : PartialSetStructure exampleLanguage (Fin 3) where
  rel := fun R => Empty.elim R
  func := fun _ _ => some output

def target : PartialSetStructure exampleLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ _ => some (Structure.imageSet projection output)

def projectedSupport : Set (Fin 2) := projection '' support

def weakProjection : support → projectedSupport :=
  fun x => ⟨projection x.1, ⟨x.1, x.2, rfl⟩⟩

/-- The UNRESTRICTED map is a genuine source-defined partial function
homomorphism: each target value is exactly the image of the source value,
and the source is defined at every unary input. -/
theorem originalPartial :
    IsOriginalPartialHomomorphism source target projection := by
  constructor
  · intro R
    exact Empty.elim R
  · intro F xs U hU
    have hEq : output = U := Option.some.inj hU
    subst U
    rfl

/-- The source support is NOT the whole preimage of its occupied target
labels: f(1)=f(2), but 2 is in S and 1 is outside. -/
theorem not_fibreSaturated :
    ¬ (∀ x : Fin 3, projection x ∈ projectedSupport → x ∈ support) := by
  intro h
  have hTarget : projection (1 : Fin 3) ∈ projectedSupport := by
    exact ⟨2, by simp [support], by simp [projection]⟩
  have hSource : (1 : Fin 3) ∈ support := h 1 hTarget
  simpa [support] using hSource

/-- The clipped source value at 0 survives as exactly the singleton
{0}, rather than preserving the original two-output fibre. -/
theorem weakSourceValue :
    (source.weakInduce support).func ()
      (fun _ : Fin 1 => (⟨0, by simp [support]⟩ : support)) =
      some {x : support | x.1 ∈ output} := by
  have hNon : output.Nonempty := ⟨0, by simp [output]⟩
  have hMeet : (output ∩ support).Nonempty :=
    ⟨0, by simp [output], by simp [support]⟩
  change weakValue support (some output) =
    some {x : support | x.1 ∈ output}
  simp [weakValue, hNon, hMeet]

/-- A target output represented by the excluded source vertex 1
still survives through the OTHER source vertex 2 with the same
target label. -/
theorem targetHasExtra :
    (target.weakInduce projectedSupport).HasOutput ()
      (weakProjection ∘
        (fun _ : Fin 1 => (⟨0, by simp [support]⟩ : support)))
      (⟨1, ⟨2, by simp [support], by simp [projection]⟩⟩ :
        projectedSupport) := by
  have hValNon : (Structure.imageSet projection output).Nonempty :=
    ⟨0, ⟨0, by simp [output], by simp [projection]⟩⟩
  have hValMeet : ((Structure.imageSet projection output) ∩
      projectedSupport).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · exact ⟨0, by simp [output], by simp [projection]⟩
    · exact ⟨0, by simp [support], by simp [projection]⟩
  refine ⟨{y : projectedSupport |
      y.1 ∈ Structure.imageSet projection output}, ?_, ?_⟩
  · change weakValue projectedSupport
      (some (Structure.imageSet projection output)) =
      some {y : projectedSupport |
        y.1 ∈ Structure.imageSet projection output}
    simp [weakValue, hValNon, hValMeet]
  · change (1 : Fin 2) ∈ Structure.imageSet projection output
    exact ⟨1, by simp [output], by simp [projection]⟩

/-- The weak IMAGE map is not an original partial homomorphism:
the target carries an extra output label 1 absent from the image
of the clipped source value {0}. -/
theorem weakProjection_not_originalPartial :
    ¬ IsOriginalPartialHomomorphism
      (source.weakInduce support) (target.weakInduce projectedSupport)
      weakProjection := by
  intro hPartial
  let xs : Fin 1 → support :=
    fun _ => ⟨0, by simp [support]⟩
  have hSource :
      (source.weakInduce support).func () xs =
        some {x : support | x.1 ∈ output} := weakSourceValue
  have hExtra :
      (⟨1, ⟨2, by simp [support], by simp [projection]⟩⟩ :
        projectedSupport) ∈
      Structure.imageSet weakProjection
        {x : support | x.1 ∈ output} := by
    have hVal :=
      hPartial.2 () xs {x : support | x.1 ∈ output} hSource
    have hOut := targetHasExtra
    obtain ⟨T, hT, hyT⟩ := hOut
    have hTval :
        T = Structure.imageSet weakProjection
          {x : support | x.1 ∈ output} :=
      Option.some.inj (hT.symm.trans hVal)
    simpa only [hTval] using hyT
  obtain ⟨z, hzU, hzy⟩ := hExtra
  have hZero : z.1 = (0 : Fin 3) := by
    fin_cases z.1 <;> simp_all [support, output]
  have hMapVal : projection z.1 = (1 : Fin 2) := by
    have h := congrArg Subtype.val hzy
    simpa only [weakProjection] using h
  have hBad : (0 : Fin 2) = 1 := by
    simpa [projection, hZero] using hMapVal
  exact (by decide : (0 : Fin 2) ≠ 1) hBad

end StructuralRamsey.PartialSetStructure.TrackAClippedImageCounterexample
