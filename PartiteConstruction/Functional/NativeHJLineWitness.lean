import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Functional.WeakInduced

/-!
# Keep the actual Hales–Jewett LINE in the functional partite witness

The verified functional partite lemma uses Hales–Jewett.finite to
choose a line W and then returns only the resulting full partite
embedding of Old into the coordinatewise power.

The actual proof therefore supplies MORE data than its conclusion:
a particular line W whose full embedding
  weak_lineEmbedding hB.1 W : B↪power B N
is the monochromatic witness. Keeping W explicit permits the
native Picture to attach copies only along LINE embeddings, rather
than every arbitrary support embedding into the power.

This is a direct theorem about genuinely SET-VALUED functions.
The power retains per-function-image TRANSVERSALITY and the
EHN projection invariant. No recursive Ramsey construction,
U-closed relational surrogate or generated closure of weak tests
is introduced.

This is just a witness-strengthening of the already verified
partite lemma, not a claim that different lines have a common
parameter coordinate.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V}

/-- The full functional Hales–Jewett partite lemma with the actual
LINE W retained in the output. All operation-output fibres of the
genuine coordinatewise power remain transversal; W's selected
embedding is a full FUNCTIONAL embedding of the old selected support. -/
theorem weak_partiteLemma_withLineWitness
    (hB : B.WeaklyPartiteOver A)
    [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧
      (power B N).WeaklyPartiteOver A ∧
      ∀ χ : FunctionalPartite.Embedding (transversal A) (power B N) → κ,
        ∃ W : Line (Letter A B) N,
          ∀ e₁ e₂ : FunctionalPartite.Embedding (transversal A) B,
            χ ((weak_lineEmbedding hB.1 W).comp e₁) =
            χ ((weak_lineEmbedding hB.1 W).comp e₂) := by
  classical
  letI : Fintype (Letter A B) := Fintype.ofFinite _
  obtain ⟨N, hN, hHJ⟩ :=
    HalesJewett.finite (α := Letter A B) (κ := κ)
  refine ⟨N, hN, power_weaklyPartiteOver hB hN, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ :=
    hHJ (fun w => χ (weak_wordEmbedding hB.1 hN w))
  refine ⟨W, ?_⟩
  intro e₁ e₂
  simpa only [weak_lineEmbedding_comp_letter hB.1 hN] using
    hW e₁ e₂

end StructuralRamsey.FunctionalPartite.Induced
