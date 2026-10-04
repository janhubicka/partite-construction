import PartiteConstruction.Iterated.ProjectedRelativeLabelledLocalTreeLike
import PartiteConstruction.Iterated.MixedRelativeLabelledGlue
import PartiteConstruction.Iterated.ControlCompletionEmbedding

/-! # Mixed gluing directly from projected histories

After correcting relative relabellings to induced embeddings, a relative
labelled request is automatic from a projected-history witness: the requested
partial boundary is already embedded by ProjectedPartialIntersections, so one
fresh copy of B can be attached over it.

This file packages the consequence needed by the mixed Picture step.  On the
base D (with the identity projection), projected histories imply the older
RelativeLabelledLocallyTreeLike oracle after compatible control completion.
Hence the checked mixed relative-labelled gluing theorem can be invoked
directly from projected histories.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}

namespace ProjectedRelativeLabelledLocallyTreeLike

/-- On the base itself, the projected relative-labelled invariant supplies
the unprojected relative-labelled oracle used by mixed gluing.

Ordinary A-copy control is completed after the relative witness has been
chosen.  The target embedding exposed by compatible control completion keeps
the distinguished target A-copy and its labels intact. -/
theorem toRelativeLabelled_identity
    [Finite U] [Finite P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    {n : ℕ}
    (h : ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id n) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n := by
  classical
  refine ⟨?_, ?_⟩
  · have hHist :
        ProjectedHistoryLocallyTreeLike
          (A := A) (D := D) (C := D) (B := B) id n :=
      h.toProjectedHistory
    have hPart :
        ProjectedPartialLocallyTreeLike
          (A := A) (D := D) (C := D) B id n :=
      hHist.toProjectedPartial
    exact hPart.toLocallyTreeLike
      hA eAB (Embedding.id D).isHomomorphismEmbedding
  · intro I hI β H hH
    let eH : Embedding (A.induce H) D :=
      β.comp (inclusion A H)
    have hproj : ∀ x : H, (id : P → P) (eH x) = β x.1 := by
      intro x
      rfl
    have hRange : ∀ x : H, eH x ∈ I := by
      intro x
      exact hH x
    obtain ⟨Y, T, hTree, f, hf, hPart, _hHist,
      target, htarget⟩ :=
      h.witness_identityLabels I hI [] β H eH hproj hRange
    have hInt :
        LocallyTreeLike.EmbeddedIntersections
          (A := A) (C := D) (T := T) I f :=
      ProjectedPartialLocallyTreeLike.embeddedIntersections
        hA (Embedding.id D).isHomomorphismEmbedding hPart
    obtain ⟨Z, T', hTree', j, hf', hctrl⟩ :=
      LocallyTreeLike.completeControl_of_embeddedIntersections_with_embedding
        (A := A) (B := B) (C := D)
        hA eAB I hTree f hf hInt
    let target' : Embedding A T' := j.comp target
    refine ⟨Z, T', hTree', j ∘ f, hf', hctrl, target', ?_⟩
    intro x
    have hx := htarget x
    change
      j (f ⟨β x.1, hH x⟩) =
        j (target x.1)
    apply congrArg j
    simpa [eH] using hx

end ProjectedRelativeLabelledLocallyTreeLike

namespace ProjectedHistoryLocallyTreeLike

/-- Projected histories on D automatically provide the relative labelled
oracle required by the mixed gluing theorem. -/
theorem toRelativeLabelled_identity
    [Finite U] [Finite P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    {n : ℕ}
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id n) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n := by
  have hRel :
      ProjectedRelativeLabelledLocallyTreeLike
        (A := A) (D := D) (C := D) (B := B) id n :=
    ProjectedRelativeLabelledLocallyTreeLike.ofProjectedHistory
      hA eAB h
  exact hRel.toRelativeLabelled_identity hA eAB

end ProjectedHistoryLocallyTreeLike

namespace ProjectedHistoryLocallyTreeLike

/-- Projected-history witnesses on the base also give the stronger
intersection-embedding control used by the reducible-overlap gluing theorem.
Compatible control completion supplies the full ambient A-copy control, while
the projected-partial certificate for each A-intersection is simply
postcomposed into the completed target. -/
theorem toIntersectionStrong
    [Finite U] [Finite P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    {n : ℕ}
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id n) :
    IntersectionStrongLocallyTreeLike A B D n := by
  classical
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, hPart, _hHist⟩ :=
    h S hS []
  have hInt :
      LocallyTreeLike.EmbeddedIntersections
        (A := A) (C := D) (T := T) S f :=
    ProjectedPartialLocallyTreeLike.embeddedIntersections
      hA (Embedding.id D).isHomomorphismEmbedding hPart
  obtain ⟨Z, T', hTree', j, hf', hctrl⟩ :=
    LocallyTreeLike.completeControl_of_embeddedIntersections_with_embedding
      (A := A) (B := B) (C := D)
      hA eAB S hTree f hf hInt
  refine ⟨Z, T', hTree', j ∘ f, hf', ?_⟩
  intro α
  obtain ⟨α', hα'⟩ := hctrl α
  let H : Set U := {a : U | α a ∈ S}
  let eH : Embedding (A.induce H) D :=
    α.comp (inclusion A H)
  have hproj : ∀ x : H, (id : P → P) (eH x) = α x.1 := by
    intro x
    rfl
  have hRange : ∀ x : H, eH x ∈ S := fun x => x.2
  obtain ⟨eHT, heHT, _hcHT⟩ :=
    hPart α H eH hproj hRange
  refine ⟨α', hα', j.comp eHT, ?_⟩
  intro x
  exact congrArg j (heHT x)

end ProjectedHistoryLocallyTreeLike

namespace LocallyTreeLike

variable {H E F C : Type v}
variable {Dsrc : RelStructure L H} {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F} {Csrc : RelStructure L C}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- The mixed projected gluing theorem with projected histories as its only
coherence hypothesis on D.  The relative labelled side completions are
constructed automatically. -/
theorem glueProjectedFull_projectedHistory
    [Finite U] [Finite P]
    [Fintype E] [Fintype F] [DecidableEq P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (p : C → P) (hp : Csrc.IsHomomorphismEmbedding D p)
    (α : Embedding A D)
    (hOverlap : ∀ d : H, ∃ a : U, p (iE (sE d)) = α a)
    (m : ℕ)
    (hD : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := D) (B := B) id m)
    (hEcard : ((Finset.univ : Finset E).image (p ∘ iE)).card ≤ m)
    (hFcard : ((Finset.univ : Finset F).image (p ∘ iF)).card ≤ m) :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam B T Target ∧
      ∃ f : C → T,
        Csrc.IsHomomorphismEmbedding Target f ∧
        ∀ γ : Embedding A Csrc,
          ∃ γ' : Embedding A Target,
            ∀ a : U, ∃ a' : U, f (γ a) = γ' a' := by
  have hRel :
      RelativeLabelledLocallyTreeLike
        (A := A) (B := B) (D := D) m :=
    hD.toRelativeLabelled_identity hA eAB
  exact glueProjectedFull_relativeLabelled
    hA hSrc p hp α hOverlap m hRel hEcard hFcard

end LocallyTreeLike
end StructuralRamsey.RelStructure
