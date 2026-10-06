import PartiteConstruction.Functional.FreeAmalgamClosed
import PartiteConstruction.Iterated.MixedOverlapExactness

/-! # Closed compatible lifts across free amalgams

For graph encodings of set-valued functions, exact overlap reflection is enough
to lift compatible induced side embeddings to an induced embedding of the
whole free amalgam.  If both side embeddings are additionally function-closed,
then the lifted embedding is function-closed as well.

The proof is most transparent on ranges: the inverse image of the lifted range
inside either target side is exactly the corresponding side-image range.
These two ranges are closed, hence the lifted range is closed in the target
free amalgam.
-/

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

open Structure

universe u v

variable {L : Language.{u}}
variable {H E F C G E₂ F₂ T : Type v}
variable {D₁ : RelStructure L.graph H}
variable {A₁ : RelStructure L.graph E}
variable {B₁ : RelStructure L.graph F}
variable {C₁ : RelStructure L.graph C}
variable {D₂ : RelStructure L.graph G}
variable {A₂ : RelStructure L.graph E₂}
variable {B₂ : RelStructure L.graph F₂}
variable {C₂ : RelStructure L.graph T}
variable {sA : Embedding D₁ A₁} {sB : Embedding D₁ B₁}
variable {iA : Embedding A₁ C₁} {iB : Embedding B₁ C₁}
variable {tA : Embedding D₂ A₂} {tB : Embedding D₂ B₂}
variable {jA : Embedding A₂ C₂} {jB : Embedding B₂ C₂}

/-- Exact compatible closed side embeddings lift to a closed embedding of the
whole source free amalgam. -/
noncomputable def liftClosedEmbedding
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (q : H → G)
    (hA : ClosedEmbedding A₁ A₂)
    (hB : ClosedEmbedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA (q d))
    (hcompatB : ∀ d, hB (sB d) = tB (q d))
    (hexA : ReflectsOverlap q sA tA hA.toEmbedding)
    (hexB : ReflectsOverlap q sB tB hB.toEmbedding) :
    ClosedEmbedding C₁ C₂ := by
  classical
  let e : Embedding C₁ C₂ :=
    liftEmbedding hSrc hTgt q
      hA.toEmbedding hB.toEmbedding
      hcompatA hcompatB hexA hexB
  have hpreA :
      jA ⁻¹' Set.range e = Set.range hA := by
    ext a₂
    constructor
    · rintro ⟨c, hc⟩
      rcases hSrc.covers c with ⟨a, hca⟩ | ⟨b, hcb⟩
      · refine ⟨a, ?_⟩
        apply jA.injective
        calc
          jA (hA a) =
              e (iA a) := by
                symm
                exact liftMap_left hSrc hTgt q
                  hA.toEmbedding hB.toEmbedding
                  hcompatA hcompatB a
          _ = e c := congrArg e hca.symm
          _ = jA a₂ := hc
      · have hcross :
            jA a₂ = jB (hB b) := by
          calc
            jA a₂ = e c := hc.symm
            _ = e (iB b) := congrArg e hcb
            _ = jB (hB b) :=
              liftMap_right hSrc hTgt q
                hA.toEmbedding hB.toEmbedding
                hcompatA hcompatB b
        obtain ⟨g, ha₂, hb⟩ :=
          (hTgt.overlap a₂ (hB b)).mp hcross
        obtain ⟨d, hbd, hqd⟩ := hexB b g hb
        refine ⟨sA d, ?_⟩
        calc
          hA (sA d) = tA (q d) := hcompatA d
          _ = tA g := congrArg tA hqd
          _ = a₂ := ha₂.symm
    · rintro ⟨a, rfl⟩
      refine ⟨iA a, ?_⟩
      exact
        (liftMap_left hSrc hTgt q
          hA.toEmbedding hB.toEmbedding
          hcompatA hcompatB a).symm
  have hpreB :
      jB ⁻¹' Set.range e = Set.range hB := by
    ext b₂
    constructor
    · rintro ⟨c, hc⟩
      rcases hSrc.covers c with ⟨a, hca⟩ | ⟨b, hcb⟩
      · have hcross :
            jA (hA a) = jB b₂ := by
          calc
            jA (hA a) =
                e (iA a) := by
                  symm
                  exact liftMap_left hSrc hTgt q
                    hA.toEmbedding hB.toEmbedding
                    hcompatA hcompatB a
            _ = e c := congrArg e hca.symm
            _ = jB b₂ := hc
        obtain ⟨g, ha, hb₂⟩ :=
          (hTgt.overlap (hA a) b₂).mp hcross
        obtain ⟨d, had, hqd⟩ := hexA a g ha
        refine ⟨sB d, ?_⟩
        calc
          hB (sB d) = tB (q d) := hcompatB d
          _ = tB g := congrArg tB hqd
          _ = b₂ := hb₂.symm
      · refine ⟨b, ?_⟩
        apply jB.injective
        calc
          jB (hB b) =
              e (iB b) := by
                symm
                exact liftMap_right hSrc hTgt q
                  hA.toEmbedding hB.toEmbedding
                  hcompatA hcompatB b
          _ = e c := congrArg e hcb.symm
          _ = jB b₂ := hc
    · rintro ⟨b, rfl⟩
      refine ⟨iB b, ?_⟩
      exact
        (liftMap_right hSrc hTgt q
          hA.toEmbedding hB.toEmbedding
          hcompatA hcompatB b).symm
  have hRangeA :
      FunctionClosedSet A₂ (Set.range hA) :=
    (hA.toEmbedding.functionClosed_iff_range).1 hA.closed
  have hRangeB :
      FunctionClosedSet B₂ (Set.range hB) :=
    (hB.toEmbedding.functionClosed_iff_range).1 hB.closed
  have hRange :
      FunctionClosedSet C₂ (Set.range e) := by
    apply (hTgt.functionClosedSet_iff (Set.range e)).2
    rw [hpreA, hpreB]
    exact ⟨hRangeA, hRangeB⟩
  refine ⟨e, ?_⟩
  exact (e.functionClosed_iff_range).2 hRange

end StructuralRamsey.RelStructure.IsFreeAmalgam
