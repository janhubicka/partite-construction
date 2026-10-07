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
