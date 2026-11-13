import PartiteConstruction.Structure.PartialSetFunctionsWeakEmbedding

/-!
# Track A: source-defined original partial maps restrict to exact clipped preimages

A global original-partial homomorphism may introduce new target-defined
applications on source-undefined inputs, so it is NOT necessarily a full
embedding. Nevertheless, taking the *literal preimage* of a target weak
vertex subset makes the clipped Option(Set)-valued weak restriction
compatible with every source-defined function value.

For f : A → B and T ⊆ B, the restricted vertex map
    (f ⁻¹' T) → T
is an original-2019 source-defined partial homomorphism
    A|ᵂ_(f⁻¹'T) → B|ᵂ_T.
The result holds for multivalued outputs, defined-empty, nullary
operations, repeated inputs and noninjective f. No reflection of
source-undefined applications, irreducibility, closure hull or
target tree completion is assumed.

An immediate exact-image corollary applies when S is saturated under
fibres of f: S = f⁻¹(f[S]). This is the property of selected
part-saturated supports in the native Hales--Jewett Picture, but it
is not asserted for arbitrary S.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- An original source-defined partial homomorphism restricts to a
source-defined partial homomorphism on the exact inverse-image clipped
weak carrier, with the same vertex map. -/
theorem IsOriginalPartialHomomorphism.clippedWeakRestrictToPreimage
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (T : Set W) :
    IsOriginalPartialHomomorphism
      (A.weakInduce (f ⁻¹' T)) (B.weakInduce T)
      (restrictMap f T) := by
  constructor
  · intro R xs hR
    change B.rel R
      (Subtype.val ∘ (restrictMap f T ∘ xs))
    have hTuple :
        Subtype.val ∘ (restrictMap f T ∘ xs) =
          f ∘ (Subtype.val ∘ xs) := by
      funext i
      rfl
    rw [hTuple]
    exact hf.1 R (Subtype.val ∘ xs) hR
  · intro F xs U hWeak
    change weakValue (f ⁻¹' T)
      (A.func F (Subtype.val ∘ xs)) = some U at hWeak
    cases hA : A.func F (Subtype.val ∘ xs) with
    | none =>
        simp [weakValue, hA] at hWeak
    | some Q =>
        have hTarget :
            B.func F (f ∘ (Subtype.val ∘ xs)) =
              some (Structure.imageSet f Q) :=
          hf.2 F (Subtype.val ∘ xs) Q hA
        have hSourceWeak :
            weakValue (f ⁻¹' T) (some Q) = some U := by
          rw [hA] at hWeak
          exact hWeak
        have hComm :
            (weakValue (f ⁻¹' T) (some Q)).map
                (Structure.imageSet (restrictMap f T)) =
              weakValue T (some (Structure.imageSet f Q)) := by
          simpa only [Option.map_some] using
            (weakValue_map_preimage f T (some Q))
        rw [hSourceWeak] at hComm
        change weakValue T
            (B.func F
              (Subtype.val ∘ (restrictMap f T ∘ xs))) =
          some (Structure.imageSet (restrictMap f T) U)
        have hTuple :
            Subtype.val ∘ (restrictMap f T ∘ xs) =
              f ∘ (Subtype.val ∘ xs) := by
          funext i
          rfl
        rw [hTuple, hTarget]
        exact hComm.symm

/-- The same exact restriction applies when the source carrier S is
specified separately, but is literally the full inverse image of T. -/
theorem IsOriginalPartialHomomorphism.clippedWeakRestrictExact
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V) (T : Set W)
    (hExact : S = f ⁻¹' T) :
    IsOriginalPartialHomomorphism (A.weakInduce S) (B.weakInduce T)
      (fun x : S => (⟨f x.1, by
        have hx : x.1 ∈ f ⁻¹' T := hExact ▸ x.2
        exact hx⟩ : T)) := by
  subst S
  exact hf.clippedWeakRestrictToPreimage T

/-- For an exact selected source support S which contains all fibres
of the map f over occupied target vertices, clipped weak images preserve
every source-defined function value on the LITERAL projected carrier f[S]. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_of_saturated
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V)
    (hSat : ∀ x : V, f x ∈ f '' S → x ∈ S) :
    IsOriginalPartialHomomorphism
      (A.weakInduce S) (B.weakInduce (f '' S))
      (fun x : S => (⟨f x.1, ⟨x.1, x.2, rfl⟩⟩ : f '' S)) := by
  have hExact : S = f ⁻¹' (f '' S) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · intro hx
      exact hSat x hx
  exact hf.clippedWeakRestrictExact S (f '' S) hExact

end StructuralRamsey.PartialSetStructure
