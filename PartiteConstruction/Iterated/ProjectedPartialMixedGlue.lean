import PartiteConstruction.Iterated.ProjectedPartialLocalTreeLike
import PartiteConstruction.Iterated.MixedRelativeLabelledGlue
import PartiteConstruction.Iterated.ControlCompletionEmbedding

/-! # Mixed gluing from projected partial-intersection coherence

Finite projected histories were introduced to synchronize the hard mixed
Picture case.  For the actual mixed gluing theorem, however, the history bits
are not needed once coherent projected partial intersections are available.

This file proves that the weaker `ProjectedPartialLocallyTreeLike` invariant
already supplies the relative-labelled side completions used by the checked
mixed gluing theorem.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P W : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}
variable {C : RelStructure L W}

namespace ProjectedPartialLocallyTreeLike

/-- Pull a projected-partial witness back through a homomorphism-embedding
when the projected image of the test fits the available size bound. -/
theorem witness_of_homEmbedding_image
    [DecidableEq P]
    {m : ℕ}
    (hD :
      ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) B id m)
    (p : W → P) (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hcard : (S.image p).card ≤ m) :
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        ProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f := by
  classical
  let I : Finset P := S.image p
  obtain ⟨Z, Target, hTree, g, hg, hPartD⟩ :=
    hD I hcard
  let pS : ↥(↑S : Set W) → ↥(↑I : Set P) :=
    fun x => ⟨p x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hToD :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding D
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hpS :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding
        (D.induce (↑I : Set P)) pS :=
    hToD.codRestrict (↑I : Set P)
      (fun x => Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩)
  let f : ↥(↑S : Set W) → Z := g ∘ pS
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f :=
    hg.comp hpS
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro β H e heproj heRange
  let eD : Embedding (A.induce H) D :=
    β.comp (inclusion A H)
  have heDproj : ∀ x, (id : P → P) (eD x) = β x.1 := by
    intro x
    rfl
  have heDRange : ∀ x, eD x ∈ I := by
    intro x
    apply Finset.mem_image.mpr
    refine ⟨e x, heRange x, ?_⟩
    exact heproj x
  obtain ⟨eT, heT, hc⟩ :=
    hPartD β H eD heDproj heDRange
  refine ⟨eT, ?_, hc⟩
  intro x
  change eT x = g (pS ⟨e x, heRange x⟩)
  rw [heT x]
  apply congrArg g
  apply Subtype.ext
  exact (heproj x).symm

/-- On the base itself, projected-partial coherence already gives the
relative-labelled oracle used in mixed gluing.  The requested boundary is
first embedded by `ProjectedPartialIntersections`; attach one fresh B-copy
over that boundary to realize the identity labels, then complete ordinary
ambient A-copy control while retaining the target embedding. -/
theorem toRelativeLabelled_identity
    [Finite U] [Finite P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    {n : ℕ}
    (h :
      ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) B id n) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n := by
  classical
  refine ⟨h.toLocallyTreeLike
    hA eAB (Embedding.id D).isHomomorphismEmbedding, ?_⟩
  intro I hI β H hH
  obtain ⟨Y, T, hTree, f, hf, hPart⟩ := h I hI
  let eH : Embedding (A.induce H) D :=
    β.comp (inclusion A H)
  have hproj : ∀ x : H, (id : P → P) (eH x) = β x.1 := by
    intro x
    rfl
  have hRange : ∀ x : H, eH x ∈ I := fun x => hH x
  obtain ⟨eHT, heHT, hcT⟩ :=
    hPart β H eH hproj hRange

  let eHB : Embedding (A.induce H) B :=
    eAB.comp (inclusion A H)
  have hcB : eHB.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA eAB eHB
    intro x
    exact ⟨x.1, rfl⟩

  let T₁ := FreeAmalgam.amalgam (A.induce H) T B eHT eHB
  let l : Embedding T T₁ :=
    FreeAmalgam.leftEmbedding (A.induce H) T B eHT eHB
  let r : Embedding B T₁ :=
    FreeAmalgam.rightEmbedding (A.induce H) T B eHT eHB
  have hTree₁ : TreeAmalgam B _ T₁ :=
    FreeAmalgam.treeAmalgam (A.induce H) T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  let f₁ : ↥(↑I : Set P) → _ := l ∘ f
  have hf₁ :
      (D.induce (↑I : Set P)).IsHomomorphismEmbedding T₁ f₁ :=
    l.isHomomorphismEmbedding.comp hf

  have hInt :
      LocallyTreeLike.EmbeddedIntersections
        (A := A) (C := D) (T := T) I f :=
    embeddedIntersections
      hA (Embedding.id D).isHomomorphismEmbedding hPart
  have hInt₁ :
      LocallyTreeLike.EmbeddedIntersections
        (A := A) (C := D) (T := T₁) I f₁ := by
    exact hInt.postcomp I f l

  obtain ⟨Z, T₂, hTree₂, j, hf₂, hctrl⟩ :=
    LocallyTreeLike.completeControl_of_embeddedIntersections_with_embedding
      (A := A) (B := B) (C := D)
      hA eAB I hTree₁ f₁ hf₁ hInt₁

  let target : Embedding A T₂ := j.comp (r.comp eAB)
  refine ⟨Z, T₂, hTree₂, j ∘ f₁, hf₂, hctrl, target, ?_⟩
  intro x
  change j (l (f ⟨β x.1, hH x⟩)) =
    j (r (eAB x.1))
  apply congrArg j
  calc
    l (f ⟨β x.1, hH x⟩) =
        l (eHT x) := congrArg l (heHT x).symm
    _ = r (eHB x) :=
      FreeAmalgam.left_right_overlap
        (A.induce H) T B eHT eHB x
    _ = r (eAB x.1) := rfl

end ProjectedPartialLocallyTreeLike

namespace LocallyTreeLike

variable {H E F C₀ : Type v}
variable {Dsrc : RelStructure L H}
variable {Esrc : RelStructure L E}
variable {Fsrc : RelStructure L F}
variable {Csrc : RelStructure L C₀}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- The mixed projected gluing theorem needs only projected-partial coherence
of the fixed base. -/
theorem glueProjectedFull_projectedPartial
    [Finite U] [Finite P]
    [Fintype E] [Fintype F] [DecidableEq P]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (hSrc : IsFreeAmalgam sE sF iE iF)
    (p : C₀ → P) (hp : Csrc.IsHomomorphismEmbedding D p)
    (α : Embedding A D)
    (hOverlap : ∀ d : H, ∃ a : U, p (iE (sE d)) = α a)
    (m : ℕ)
    (hD :
      ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := D) B id m)
    (hEcard : ((Finset.univ : Finset E).image (p ∘ iE)).card ≤ m)
    (hFcard : ((Finset.univ : Finset F).image (p ∘ iF)).card ≤ m) :
    ∃ (T : Type v) (Target : RelStructure L T),
      TreeAmalgam B T Target ∧
      ∃ f : C₀ → T,
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
