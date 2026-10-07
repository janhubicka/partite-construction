import PartiteConstruction.Functional.FreeAmalgamHistoryInduction
import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion

/-! # Pure functional history completions

A projected-history tree completion of a whole structure restricts along
any full embedding.  In particular, a finite source whose embedding into
a free amalgam lies wholly inside one side inherits the side's histories,
without synchronizing another target tree.

A generator-bounded projected-history invariant also gives a witness on
the entire finite source whenever the source itself is generated within the
bound.  Together these are the two pure branches of the placement-sensitive
functional free-amalgam induction.
-/

namespace StructuralRamsey.Structure

universe u v

namespace HasProjectedHistoryTreeCompletion

variable {L : Language.{u}} {V W X P : Type v}
variable {Base : Structure L V}
variable {C : Structure L W} {D : Structure L X}
variable {p : W → P}

/-- Pull back a projected-history completion through a full embedding. -/
theorem pullback_embedding
    (h : HasProjectedHistoryTreeCompletion Base C p)
    (e : Embedding D C) :
    HasProjectedHistoryTreeCompletion Base D (p ∘ e) := by
  intro history
  obtain ⟨Z, Target, hTree, f, hf, hHist⟩ := h history
  let g : X → Z := f ∘ e
  have hg : D.IsHomomorphismEmbedding Target g :=
    hf.comp e.isHomomorphismEmbedding
  have hHistG :
      ∀ K ∈ history, ∀ x y : X,
        g x = g y → ((p ∘ e) x ∈ K ↔ (p ∘ e) y ∈ K) := by
    intro K hK x y hxy
    exact hHist K hK (e x) (e y) hxy
  exact ⟨Z, Target, hTree, g, hg, hHistG⟩

end HasProjectedHistoryTreeCompletion


namespace FunctionalProjectedHistoryTreeLike

variable {L : Language.{u}} {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}
variable {p : W → P} {n : ℕ}

/-- A finite entire structure has projected-history tree completions as
soon as it satisfies the generator-bounded history invariant at a rank
large enough to generate its carrier. -/
theorem toFullProjectedHistoryCompletion
    [Fintype W]
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hgen : C.GeneratedByAtMost n) :
    HasProjectedHistoryTreeCompletion Base C p := by
  classical
  let S : Finset W := Finset.univ
  have hS : C.IsClosed (↑S : Set W) := by
    intro F x _ y _
    simp [S]
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  let allEmb : Embedding C Small :=
    (Embedding.id C).factorWithMap inc
      (fun x => ⟨x, Finset.mem_univ x⟩)
      (fun _ => rfl)
  have hsurj : Function.Surjective allEmb := by
    intro y
    refine ⟨y.1, ?_⟩
    apply Subtype.ext
    rfl
  have hgenSmall : Small.GeneratedByAtMost n :=
    hgen.of_surjective_embedding allEmb hsurj
  intro history
  obtain ⟨Z, Target, hTree, f₀, hf₀, _hPart, hHist₀⟩ :=
    h S hS hgenSmall history
  let f : W → Z := f₀ ∘ allEmb
  have hf : C.IsHomomorphismEmbedding Target f :=
    hf₀.comp allEmb.isHomomorphismEmbedding
  have hHist :
      ∀ K ∈ history, ∀ x y : W,
        f x = f y → (p x ∈ K ↔ p y ∈ K) := by
    intro K hK x y hxy
    exact hHist₀ K hK (allEmb x) (allEmb y) hxy
  exact ⟨Z, Target, hTree, f, hf, hHist⟩

end FunctionalProjectedHistoryTreeLike

end StructuralRamsey.Structure


namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C VB P : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C} {Base : Structure L VB}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- In the projected-history completion induction, both pure branches
follow from full history completability of their respective ambient sides.
The only extra input is the genuinely mixed common-separator lifting step.

This is useful for the functional Picture stage: the old stage and the
Hales--Jewett core supply the two pure side properties, so no further
case-specific completion construction is needed there. -/
theorem finiteHistoryCompletion_of_sides_and_relativeMixed
    [Fintype P] [Nonempty P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (p : C → P)
    (hSideLeft :
      HasProjectedHistoryTreeCompletion Base Left (p ∘ iL))
    (hSideRight :
      HasProjectedHistoryTreeCompletion Base Right (p ∘ iR))
    (hMixed :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        HasProjectedHistoryTreeCompletion Base pb.common
          (p ∘ (e.comp (pb.leftIn.comp pb.toLeft))) →
        HasProjectedHistoryTreeCompletion Base pb.left
          (p ∘ (e.comp pb.leftIn)) →
        HasProjectedHistoryTreeCompletion Base pb.right
          (p ∘ (e.comp pb.rightIn)) →
        ∀ history : List (Set P),
          ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
            TreeAmalgam Base G Start ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toLeft q ((p ∘ e) ∘ pb.leftIn)
              (history ++ singletonProjectedHistory P) ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toRight q ((p ∘ e) ∘ pb.rightIn)
              (history ++ singletonProjectedHistory P)) :
    ∀ {X : Type v} [Finite X]
      (D : Structure L X) (e : Embedding D Whole),
      HasProjectedHistoryTreeCompletion Base D (p ∘ e) := by
  classical
  apply finiteHistoryCompletion_of_relativeMixed hSrc p
  · intro X _ D e hRange
    let j : Embedding D Left := e.factorThroughRange iL hRange
    have hproj : ((p ∘ iL) ∘ j) = (p ∘ e) := by
      funext x
      change p (iL (j x)) = p (e x)
      exact congrArg p (Classical.choose_spec (hRange x)).symm
    rw [← hproj]
    exact hSideLeft.pullback_embedding j
  · intro X _ D e hRange
    let j : Embedding D Right := e.factorThroughRange iR hRange
    have hproj : ((p ∘ iR) ∘ j) = (p ∘ e) := by
      funext x
      change p (iR (j x)) = p (e x)
      exact congrArg p (Classical.choose_spec (hRange x)).symm
    rw [← hproj]
    exact hSideRight.pullback_embedding j
  · exact hMixed

end StructuralRamsey.Structure.IsFreeAmalgam
