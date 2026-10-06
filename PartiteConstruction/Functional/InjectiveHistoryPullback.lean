import PartiteConstruction.Functional.HistoryTreeCompletion
import PartiteConstruction.Functional.ClosedGeneratorRank

/-! # Pulling synchronized functional histories through an injective test

An EHN projection need not be a full embedding globally.  On a fixed closed
test, however, if the projection is injective and already a full
homomorphism-embedding there, the synchronized local-tree witness can be
pulled back from the closed image in the outer structure D.

Projected histories are unchanged.  A source-history set H is transported to
the image of H intersect the tested set; injectivity on the test makes
membership reflect back exactly.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {C : Structure L W}
variable {Base : Structure L V}
variable {p : W → P}
variable {n : ℕ}

namespace FunctionalHistoryTreeLike

/-- Test-local pullback through a full homomorphism-embedding which is
injective on the tested finite set. -/
theorem witness_pullback_injective
    (hD : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := D) (Base := Base) id n)
    (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (hinjS :
      ∀ x ∈ S, ∀ y ∈ S, p x = p y → x = y)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        IsHomomorphismEmbedding
          (C.induce (↑S : Set W) hS) Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  let q : ↥(↑S : Set W) → P := p ∘ inc
  have hqIHE : IsHomomorphismEmbedding Small D q :=
    hp.comp inc.isHomomorphismEmbedding
  have hqHom : Small.IsHomomorphism D q :=
    hqIHE.1

  let I : Finset P := S.image p
  have hrange : Set.range q = (↑I : Set P) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
      let xs : ↥(↑S : Set W) := ⟨x, hxS⟩
      refine ⟨xs, ?_⟩
      exact hxy
  have hIclosed : D.IsClosed (↑I : Set P) := by
    rw [← hrange]
    exact hqHom.range_isClosed
  let R := D.induce (↑I : Set P) hIclosed
  let incR : Embedding R D :=
    inclusion D (↑I : Set P) hIclosed
  let qR : ↥(↑S : Set W) → ↥(↑I : Set P) :=
    fun x => ⟨q x, by
      apply Finset.mem_image.mpr
      exact ⟨x.1, x.2, rfl⟩⟩

  have hqRHom : Small.IsHomomorphism R qR :=
    hqHom.codRestrict (↑I : Set P) hIclosed (fun x => by
      apply Finset.mem_image.mpr
      exact ⟨x.1, x.2, rfl⟩)

  have hqRIHE : Small.IsHomomorphismEmbedding R qR := by
    refine ⟨hqRHom, ?_⟩
    intro X E hE e
    obtain ⟨g, hg⟩ := hqIHE.2 E hE e
    have hgrange :
        ∀ z : X, ∃ r : ↥(↑I : Set P), g z = incR r := by
      intro z
      have hz : g z = q (e z) := hg z
      let r : ↥(↑I : Set P) :=
        ⟨q (e z), by
          apply Finset.mem_image.mpr
          exact ⟨(e z).1, (e z).2, rfl⟩⟩
      exact ⟨r, hz⟩
    let gr : Embedding E R :=
      g.factorThroughClosedRange incR hgrange
    refine ⟨gr, ?_⟩
    intro z
    apply Subtype.ext
    have hfactor :
        incR (gr z) = g z :=
      Embedding.factorThroughClosedRange_spec g incR hgrange z
    calc
      (gr z).1 = g z := hfactor
      _ = q (e z) := hg z
      _ = (qR (e z)).1 := rfl

  have hIgen :
      R.GeneratedByAtMost n := by
    have hgenRange :=
      homRange_generatedByAtMost hqHom hgen
    let Range :=
      D.induce (Set.range q) hqHom.range_isClosed
    let incRange : Embedding Range D :=
      inclusion D (Set.range q) hqHom.range_isClosed
    have hinto :
        ∀ x : ↥(Set.range q),
          ∃ y : ↥(↑I : Set P), incRange x = incR y := by
      intro x
      have hxI : x.1 ∈ (↑I : Set P) := by
        rw [← hrange]
        exact x.2
      exact ⟨⟨x.1, hxI⟩, rfl⟩
    let eRange : Embedding Range R :=
      incRange.factorThroughClosedRange incR hinto
    have heSurj : Function.Surjective eRange := by
      intro y
      have hyRange : y.1 ∈ Set.range q := by
        rw [hrange]
        exact y.2
      let x : ↥(Set.range q) := ⟨y.1, hyRange⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      have hs :=
        Embedding.factorThroughClosedRange_spec
          incRange incR hinto x
      change (eRange x).1 = x.1 at hs
      exact hs
    have hgenRange' : Range.GeneratedByAtMost n := by
      simpa [Range] using hgenRange
    exact hgenRange'.of_surjective_embedding eRange heSurj

  let sourceHistoryD : List (Set P) :=
    sourceHistory.map
      (fun H => p '' (H ∩ (↑S : Set W)))

  obtain ⟨Z, Target, hTree, fR, hfR, hPartR, hProjR, hSrcR⟩ :=
    hD I hIclosed hIgen projectedHistory sourceHistoryD

  let f : ↥(↑S : Set W) → Z := fR ∘ qR
  have hf :
      Small.IsHomomorphismEmbedding Target f :=
    hfR.comp hqRIHE

  have hPart :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := Target)
        p S f := by
    intro β H hH e hproj hRange
    let eD : Embedding (A.induce H hH) D :=
      β.comp (inclusion A H hH)
    have hRangeD : ∀ x, eD x ∈ I := by
      intro x
      apply Finset.mem_image.mpr
      refine ⟨e x, hRange x, ?_⟩
      change p (e x) = β x.1
      exact hproj x
    have hprojD : ∀ x, (id : P → P) (eD x) = β x.1 := by
      intro x
      rfl
    obtain ⟨eHT, heHT, hcHT⟩ :=
      hPartR β H hH eD hprojD hRangeD
    refine ⟨eHT, ?_, hcHT⟩
    intro x
    change eHT x = fR (qR ⟨e x, hRange x⟩)
    have hx :
        (⟨eD x, hRangeD x⟩ : ↥(↑I : Set P)) =
          qR ⟨e x, hRange x⟩ := by
      apply Subtype.ext
      change β x.1 = p (e x)
      exact (hproj x).symm
    rw [← hx]
    exact heHT x

  have hProj :
      FunctionalRespectsProjectedHistory
        p S f projectedHistory := by
    intro K hK x y hxy
    have h :=
      hProjR K hK (qR x) (qR y) hxy
    change (p x.1 ∈ K ↔ p y.1 ∈ K) at h
    exact h

  have hSrc :
      FunctionalRespectsSourceHistory
        S f sourceHistory := by
    intro H hH x y hxy
    let HD : Set P := p '' (H ∩ (↑S : Set W))
    have hHD : HD ∈ sourceHistoryD := by
      apply List.mem_map.mpr
      exact ⟨H, hH, rfl⟩
    have hmem :=
      hSrcR HD hHD (qR x) (qR y) hxy
    have hx :
        (qR x).1 ∈ HD ↔ x.1 ∈ H := by
      constructor
      · rintro ⟨z, ⟨hzH, hzS⟩, hpz⟩
        have hzx : z = x.1 :=
          hinjS z hzS x.1 x.2 hpz
        simpa [hzx] using hzH
      · intro hxH
        exact ⟨x.1, ⟨hxH, x.2⟩, rfl⟩
    have hy :
        (qR y).1 ∈ HD ↔ y.1 ∈ H := by
      constructor
      · rintro ⟨z, ⟨hzH, hzS⟩, hpz⟩
        have hzy : z = y.1 :=
          hinjS z hzS y.1 y.2 hpz
        simpa [hzy] using hzH
      · intro hyH
        exact ⟨y.1, ⟨hyH, y.2⟩, rfl⟩
    exact hx.symm.trans (hmem.trans hy)

  exact ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc⟩

end FunctionalHistoryTreeLike
end StructuralRamsey.Structure
