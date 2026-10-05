import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion
import PartiteConstruction.Functional.ControlCompletion

/-! # Combined projected/source histories for functional local tree completion

The relational sparsening proof only needs histories of subsets of the ambient
part structure D.  For set-valued functions this is not sufficient when two
source vertices occupy the same part: fibre-surjectivity in a mixed free
amalgam also needs to know that points outside the actual source overlap are
not identified with points inside it.

Accordingly the functional diary carries two finite histories:
* projected subsets of D, for the existing partite bookkeeping;
* actual subsets of the current source C, for root isolation.

The final local tree-completion statement forgets both histories.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}

/-- Functional projected-history invariant strengthened by arbitrary finite
source-side history. -/
def FunctionalHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ (projectedHistory : List (Set P))
      (sourceHistory : List (Set W)),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory

namespace FunctionalHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Forget source history. -/
theorem toProjectedHistory
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  intro S hS hgen history
  obtain ⟨Z, T, hTree, f, hf, hPart, hProj, _⟩ :=
    h S hS hgen history []
  exact ⟨Z, T, hTree, f, hf, hPart, hProj⟩

/-- Forget all diary data. -/
theorem toLocallyClosedTreeCompletable
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyClosedTreeCompletable Base C n :=
  h.toProjectedHistory.toLocallyClosedTreeCompletable

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hgen hp hs
  exact h S hS (hgen.mono hmn) hp hs

/-- The combined history invariant pulls back along a full embedding.
Projected histories stay in the same ambient part structure; source histories
are transported by direct image under the embedding. -/
theorem pullback_embedding
    {X : Type v} {C' : Structure L X}
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (e : Embedding C' C) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C') (Base := Base) (p ∘ e) n := by
  classical
  intro S hS hgen projectedHistory sourceHistory
  let I : Finset W := S.image e
  have hIclosed : C.IsClosed (↑I : Set W) := by
    have hset :
        (↑I : Set W) = imageSet e (↑S : Set X) := by
      ext y
      simp [I, imageSet]
    rw [hset]
    exact e.image_isClosed hS
  let incS : Embedding (C'.induce (↑S : Set X) hS) C' :=
    inclusion C' (↑S : Set X) hS
  let incI : Embedding (C.induce (↑I : Set W) hIclosed) C :=
    inclusion C (↑I : Set W) hIclosed
  let j : Embedding (C'.induce (↑S : Set X) hS) C :=
    e.comp incS
  have hrange :
      ∀ x : ↥(↑S : Set X),
        ∃ y : ↥(↑I : Set W), j x = incI y := by
    intro x
    let y : ↥(↑I : Set W) :=
      ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
    exact ⟨y, rfl⟩
  let ee : Embedding
      (C'.induce (↑S : Set X) hS)
      (C.induce (↑I : Set W) hIclosed) :=
    j.factorThroughClosedRange incI hrange
  have hee (x : ↥(↑S : Set X)) :
      (ee x).1 = e x.1 := by
    have hx : j x = incI (ee x) := by
      change j x = incI (Classical.choose (hrange x))
      exact Classical.choose_spec (hrange x)
    exact hx.symm
  have heesurj : Function.Surjective ee := by
    intro y
    have hy : y.1 ∈ I := y.2
    rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
    let xs : ↥(↑S : Set X) := ⟨x, hxS⟩
    refine ⟨xs, ?_⟩
    apply Subtype.ext
    calc
      (ee xs).1 = e x := hee xs
      _ = y.1 := hxy
  have hIgen :
      (C.induce (↑I : Set W) hIclosed).GeneratedByAtMost n :=
    hgen.of_surjective_embedding ee heesurj
  let sourceHistoryI : List (Set W) :=
    sourceHistory.map (fun H => e '' H)
  obtain ⟨Z, T, hTree, fI, hfI, hPartI, hProjI, hSrcI⟩ :=
    h I hIclosed hIgen projectedHistory sourceHistoryI
  let f : ↥(↑S : Set X) → Z := fI ∘ ee
  have hf :
      (C'.induce (↑S : Set X) hS).IsHomomorphismEmbedding T f := by
    exact hfI.comp ee.isHomomorphismEmbedding
  have hPart :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C') (T := T)
        (p ∘ e) S f := by
    intro β H hH a hproj hRange
    let aC : Embedding (A.induce H hH) C := e.comp a
    have hprojC : ∀ x, p (aC x) = β x.1 := by
      intro x
      exact hproj x
    have hRangeC : ∀ x, aC x ∈ I := by
      intro x
      exact Finset.mem_image.mpr ⟨a x, hRange x, rfl⟩
    obtain ⟨eHT, heHT, hcHT⟩ :=
      hPartI β H hH aC hprojC hRangeC
    refine ⟨eHT, ?_, hcHT⟩
    intro x
    change eHT x = fI (ee ⟨a x, hRange x⟩)
    have himage :
        (⟨aC x, hRangeC x⟩ : ↥(↑I : Set W)) =
          ee ⟨a x, hRange x⟩ := by
      apply Subtype.ext
      symm
      exact hee ⟨a x, hRange x⟩
    rw [← himage]
    exact heHT x
  have hProj :
      FunctionalRespectsProjectedHistory
        (p ∘ e) S f projectedHistory := by
    intro H hH x y hxy
    have hxyI : fI (ee x) = fI (ee y) := hxy
    have hmem := hProjI H hH (ee x) (ee y) hxyI
    simpa [Function.comp_apply, hee x, hee y] using hmem
  have hSrc :
      FunctionalRespectsSourceHistory S f sourceHistory := by
    intro H hH x y hxy
    have hHI : e '' H ∈ sourceHistoryI := by
      simp [sourceHistoryI, hH]
    have hxyI : fI (ee x) = fI (ee y) := hxy
    have hmem := hSrcI (e '' H) hHI (ee x) (ee y) hxyI
    have hx :
        (ee x).1 ∈ e '' H ↔ x.1 ∈ H := by
      rw [hee x]
      constructor
      · rintro ⟨z, hz, hez⟩
        have : z = x.1 := e.injective hez
        simpa [this] using hz
      · intro hxH
        exact ⟨x.1, hxH, rfl⟩
    have hy :
        (ee y).1 ∈ e '' H ↔ y.1 ∈ H := by
      rw [hee y]
      constructor
      · rintro ⟨z, hz, hez⟩
        have : z = y.1 := e.injective hez
        simpa [this] using hz
      · intro hyH
        exact ⟨y.1, hyH, rfl⟩
    exact hx.symm.trans (hmem.trans hy)
  exact ⟨Z, T, hTree, f, hf, hPart, hProj, hSrc⟩

/-- If the witness map is injective then it respects every source history. -/
theorem respectsSourceHistory_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (history : List (Set W)) :
    FunctionalRespectsSourceHistory S f history := by
  intro H _ x y hxy
  have hxy' : x = y := hf hxy
  subst y
  rfl

/-- If equality in the target already implies equality of source vertices,
both kinds of finite history are automatic. -/
theorem histories_of_injective
    {Y : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hf : Function.Injective f)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    FunctionalRespectsProjectedHistory p S f projectedHistory ∧
      FunctionalRespectsSourceHistory S f sourceHistory := by
  constructor
  · intro H _ x y hxy
    have hxy' : x = y := hf hxy
    subst y
    rfl
  · exact respectsSourceHistory_of_injective hf sourceHistory

end FunctionalHistoryTreeLike

end StructuralRamsey.Structure
