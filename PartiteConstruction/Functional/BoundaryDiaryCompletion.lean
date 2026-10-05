import PartiteConstruction.Functional.BoundaryDiary
import PartiteConstruction.Functional.RelativeHistoryTreeCompletion

/-! # Completing a finite functional boundary diary

A relative-history witness contains projected-partial embeddings for every
relevant closed A-boundary.  Because the source is finite, any finite list of
such boundaries can be realized simultaneously: request all boundary ranges
in the source history, then attach one fresh Base-copy over each already
embedded boundary.  Earlier isolated copies survive by target
postcomposition.
-/

namespace StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike

universe u v

variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}
variable {p : W → P} {n : ℕ}

/-- Whole-structure witness satisfying a finite projected boundary diary. -/
theorem fullWitness_withBoundaryDiary
    [Fintype W]
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hgen : C.GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W))
    (requests : List (ProjectedBoundaryRequest A D C p)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : W → Z,
        C.IsHomomorphismEmbedding Target f ∧
        (∀ Hset ∈ projectedHistory, ∀ x y : W,
          f x = f y → (p x ∈ Hset ↔ p y ∈ Hset)) ∧
        (∀ Hset ∈ sourceHistory, ∀ x y : W,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) ∧
        ∀ r ∈ requests, IsolatedBoundary r.boundary Target f := by
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

  let boundaryHistory : List (Set W) :=
    requests.map (fun r => Set.range r.boundary.embedding)
  let allSourceHistory : List (Set W) :=
    sourceHistory ++ boundaryHistory

  obtain ⟨Y, T, hTree, f0, hf0, hPart0, hProj0, hSrc0⟩ :=
    h.toHistory S hS hgenSmall projectedHistory allSourceHistory

  let f : W → Y := f0 ∘ allEmb
  have hf : C.IsHomomorphismEmbedding T f :=
    hf0.comp allEmb.isHomomorphismEmbedding

  have hProj :
      ∀ Hset ∈ projectedHistory, ∀ x y : W,
        f x = f y → (p x ∈ Hset ↔ p y ∈ Hset) := by
    intro Hset hmem x y hxy
    exact hProj0 Hset hmem (allEmb x) (allEmb y) hxy

  have hSrc :
      ∀ Hset ∈ sourceHistory, ∀ x y : W,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) := by
    intro Hset hmem x y hxy
    have hall : Hset ∈ allSourceHistory := by
      apply List.mem_append.mpr
      exact Or.inl hmem
    exact hSrc0 Hset hall (allEmb x) (allEmb y) hxy

  have hBoundaryRange
      (r : ProjectedBoundaryRequest A D C p)
      (hr : r ∈ requests) :
      ∀ x y : W, f x = f y →
        (x ∈ Set.range r.boundary.embedding ↔
         y ∈ Set.range r.boundary.embedding) := by
    intro x y hxy
    have hmem :
        Set.range r.boundary.embedding ∈ boundaryHistory := by
      apply List.mem_map.mpr
      exact ⟨r, hr, rfl⟩
    have hall :
        Set.range r.boundary.embedding ∈ allSourceHistory := by
      apply List.mem_append.mpr
      exact Or.inr hmem
    exact hSrc0 (Set.range r.boundary.embedding) hall
      (allEmb x) (allEmb y) hxy

  have requestEmbedding
      (r : ProjectedBoundaryRequest A D C p) :
      ∃ eRT : Embedding
          (A.induce r.boundary.support r.boundary.supportClosed) T,
        (∀ x, eRT x = f (r.boundary.embedding x)) ∧
        eRT.ContainedInIrreducible := by
    have hRange :
        ∀ x, r.boundary.embedding x ∈ S := by
      intro x
      exact Finset.mem_univ _
    obtain ⟨eRT, heRT, hcRT⟩ :=
      hPart0 r.beta r.boundary.support r.boundary.supportClosed
        r.boundary.embedding r.projection hRange
    refine ⟨eRT, ?_, hcRT⟩
    intro x
    have hx := heRT x
    change eRT x = f0 (allEmb (r.boundary.embedding x))
    exact hx

  have aux :
      ∀ rs : List (ProjectedBoundaryRequest A D C p),
        ∃ (Z0 : Type v) (T0 : Structure L Z0),
          TreeAmalgam Base Z0 T0 ∧
          ∃ j : Embedding T T0,
            ∀ r ∈ rs,
              IsolatedBoundary r.boundary T0 (j ∘ f) := by
    intro rs
    induction rs with
    | nil =>
        refine ⟨Y, T, hTree, Embedding.id T, ?_⟩
        intro r hr
        exact (List.not_mem_nil hr).elim
    | cons r rs ih =>
        obtain ⟨Z1, T1, hTree1, j1, hDiary1⟩ := ih
        obtain ⟨eRT, heRT, hcRT⟩ := requestEmbedding r
        let Hstr :=
          A.induce r.boundary.support r.boundary.supportClosed
        let eRoot : Embedding Hstr T1 := j1.comp eRT
        let eBase : Embedding Hstr Base :=
          eAB.comp
            (inclusion A r.boundary.support r.boundary.supportClosed)
        have hcRoot : eRoot.ContainedInIrreducible :=
          hcRT.postcomp j1
        have hcBase : eBase.ContainedInIrreducible := by
          refine ⟨U, A, hA, eAB, ?_⟩
          intro x
          exact ⟨x.1, rfl⟩
        let T2 := FreeAmalgam.amalgam Hstr T1 Base eRoot eBase
        let l : Embedding T1 T2 :=
          FreeAmalgam.leftEmbedding Hstr T1 Base eRoot eBase
        let rb : Embedding Base T2 :=
          FreeAmalgam.rightEmbedding Hstr T1 Base eRoot eBase
        have hfree : IsFreeAmalgam eRoot eBase l rb :=
          FreeAmalgam.isFreeAmalgam Hstr T1 Base eRoot eBase
        have hTree2 : TreeAmalgam Base _ T2 :=
          FreeAmalgam.treeAmalgam Hstr T1 Base eRoot eBase Base
            hTree1
            (TreeAmalgam.copy (Embedding.id Base) (by
              intro b
              exact ⟨b, rfl⟩))
            hcRoot hcBase
        let j2 : Embedding T T2 := l.comp j1
        have hOld :
            ∀ q ∈ rs,
              IsolatedBoundary q.boundary T2 (j2 ∘ f) := by
          intro q hq
          have hq0 := hDiary1 q hq
          simpa [j2, Function.comp_def] using hq0.postcompTarget l
        have hNew :
            IsolatedBoundary r.boundary T2 (j2 ∘ f) := by
          let targetCopy : Embedding A T2 := rb.comp eAB
          refine ⟨targetCopy, ?_, ?_⟩
          · intro x
            change l (j1 (f (r.boundary.embedding x))) =
              rb (eAB x.1)
            calc
              l (j1 (f (r.boundary.embedding x))) =
                  l (j1 (eRT x)) :=
                congrArg (fun z => l (j1 z)) (heRT x).symm
              _ = l (eRoot x) := rfl
              _ = rb (eBase x) :=
                (hfree.overlap (eRoot x) (eBase x)).mpr
                  ⟨x, rfl, rfl⟩
              _ = rb (eAB x.1) := rfl
          · intro y a hya
            have hcross :
                l (j1 (f y)) = rb (eAB a) := by
              exact hya
            obtain ⟨z, hzRoot, hzBase⟩ :=
              (hfree.overlap (j1 (f y)) (eAB a)).mp hcross
            have ha : z.1 = a := by
              apply eAB.injective
              exact hzBase
            have hEq0 :
                f y = f (r.boundary.embedding z) := by
              apply j1.injective
              calc
                j1 (f y) = eRoot z := hzRoot
                _ = j1 (eRT z) := rfl
                _ = j1 (f (r.boundary.embedding z)) :=
                  congrArg j1 (heRT z)
            have hyRange :
                y ∈ Set.range r.boundary.embedding :=
              (hBoundaryRange r (by simp) y
                (r.boundary.embedding z) hEq0).2 ⟨z, rfl⟩
            rcases hyRange with ⟨z', hyz'⟩
            have hzz : z' = z := by
              apply eRT.injective
              calc
                eRT z' = f (r.boundary.embedding z') := heRT z'
                _ = f y := congrArg f hyz'.symm
                _ = f (r.boundary.embedding z) := hEq0
                _ = eRT z := (heRT z).symm
            subst z'
            refine ⟨z, ?_, ha⟩
            exact hyz'.symm
        refine ⟨_, T2, hTree2, j2, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hNew
        · exact hOld q hq

  obtain ⟨Z, Target, hTree', j, hDiary⟩ := aux requests
  let f' : W → Z := j ∘ f
  have hf' : C.IsHomomorphismEmbedding Target f' :=
    j.isHomomorphismEmbedding.comp hf
  have hProj' :
      ∀ Hset ∈ projectedHistory, ∀ x y : W,
        f' x = f' y → (p x ∈ Hset ↔ p y ∈ Hset) := by
    intro Hset hmem x y hxy
    exact hProj Hset hmem x y (j.injective hxy)
  have hSrc' :
      ∀ Hset ∈ sourceHistory, ∀ x y : W,
        f' x = f' y → (x ∈ Hset ↔ y ∈ Hset) := by
    intro Hset hmem x y hxy
    exact hSrc Hset hmem x y (j.injective hxy)
  exact ⟨Z, Target, hTree', f', hf', hProj', hSrc', hDiary⟩

end StructuralRamsey.Structure.FunctionalRelativeHistoryTreeLike
