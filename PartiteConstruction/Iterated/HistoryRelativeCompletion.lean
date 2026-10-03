import PartiteConstruction.Iterated.ProjectedHistoryLocalTreeLike
import PartiteConstruction.Iterated.ControlCompletionEmbedding

/-! # Identity-labelled relative completions from projected history

A projected-history witness already carries an induced embedding of every
projection-compatible partial A-boundary into the target tree, with its image
contained in an irreducible target piece.

Therefore an identity-labelled relative completion is obtained by one allowed
tree-amalgam step: attach a fresh copy of B over that boundary, using the
existing target boundary embedding on the old side and the canonical
A|H -> A -> B embedding on the fresh side.

The old target embeds into the new target, so projected-partial certificates
and finite history constraints survive by postcomposition.
-/
namespace StructuralRamsey.RelStructure.ProjectedHistoryLocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V P W : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}
variable {C : RelStructure L W}
variable {p : W → P}
variable {n : ℕ}

/-- Force identity A-labels on one projection-compatible partial boundary
while retaining the full projected-partial and history witness data. -/
theorem witness_identityRequest
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n)
    (S : Finset W) (hS : S.card ≤ n)
    (history : List (Set P))
    (β : Embedding A D) (H : Set U)
    (e : Embedding (A.induce H) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S) :
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        ProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        RespectsProjectedHistory p S f history ∧
        ∃ targetCopy : Embedding A Target,
          ∀ x : ↥H, f ⟨e x, hRange x⟩ = targetCopy x.1 := by
  classical
  obtain ⟨Y, T, hTree, f₀, hf₀, hPart₀, hHist₀⟩ :=
    h S hS history
  obtain ⟨eHT, heHT, hcT⟩ :=
    hPart₀ β H e hproj hRange
  let eHB : Embedding (A.induce H) B :=
    eAB.comp (inclusion A H)
  have hcB : eHB.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA eAB eHB
    intro x
    exact ⟨x.1, rfl⟩
  let T' := FreeAmalgam.amalgam (A.induce H) T B eHT eHB
  let j : Embedding T T' :=
    FreeAmalgam.leftEmbedding (A.induce H) T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding (A.induce H) T B eHT eHB
  have hTree' :
      TreeAmalgam B
        (FreeAmalgam.Vertex (A.induce H) T B eHT eHB) T' :=
    FreeAmalgam.treeAmalgam (A.induce H) T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  let f : ↥(↑S : Set W) →
      FreeAmalgam.Vertex (A.induce H) T B eHT eHB :=
    j ∘ f₀
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f :=
    j.isHomomorphismEmbedding.comp hf₀

  have hPart :
      ProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T') p S f := by
    intro γ K q hqproj hqRange
    obtain ⟨qT, hqT, hc⟩ :=
      hPart₀ γ K q hqproj hqRange
    refine ⟨j.comp qT, ?_, hc.postcomp j⟩
    intro x
    exact congrArg j (hqT x)

  have hHist :
      RespectsProjectedHistory p S f history := by
    intro K hK x y hxy
    apply hHist₀ K hK x y
    exact j.injective hxy

  let targetCopy : Embedding A T' := r.comp eAB
  have hlabel :
      ∀ x : ↥H, f ⟨e x, hRange x⟩ = targetCopy x.1 := by
    intro x
    change j (f₀ ⟨e x, hRange x⟩) = r (eAB x.1)
    calc
      j (f₀ ⟨e x, hRange x⟩) = j (eHT x) :=
        congrArg j (heHT x).symm
      _ = r (eHB x) :=
        FreeAmalgam.left_right_overlap
          (A.induce H) T B eHT eHB x
      _ = r (eAB x.1) := rfl

  exact ⟨_, T', hTree', f, hf, hPart, hHist,
    targetCopy, hlabel⟩

end StructuralRamsey.RelStructure.ProjectedHistoryLocallyTreeLike
