import PartiteConstruction.Functional.GeneratedTreeCompletion
import PartiteConstruction.Functional.ClosedAttachmentDecompose

/-! # Projected-history tree witnesses for closed functional tests

This is the function-language counterpart of the relational
ProjectedPartialIntersections / ProjectedHistoryLocallyTreeLike invariant.

The important simplification is that every partial A-intersection occurring
here is a genuine closed substructure of A.  In the function language this is
forced automatically when a closed tested substructure meets a full A-copy:
the intersection is the preimage of a closed set under a full embedding.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W Y V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {T : Structure L Y}
variable {Base : Structure L V}

/-- Coherent embeddings of all closed tested pieces of ambient A-copies whose
projection is the restriction of a genuine full A -> D embedding. -/
def FunctionalProjectedPartialIntersections
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S),
    ∃ eHT : Embedding (A.induce H hH) T,
      (∀ x, eHT x = f ⟨e x, hRange x⟩) ∧
      eHT.ContainedInIrreducible

/-- Equality in a target witness may also be required to remember
finite source-side subsets directly.  This is stronger than projected history
when several source vertices lie in the same part, and it is exactly what
full set-valued functions need for root isolation in a mixed free-amalgam
step. -/
def FunctionalRespectsSourceHistory
    (S : Finset W)
    (f : ↥(↑S : Set W) → Y)
    (history : List (Set W)) : Prop :=
  ∀ H ∈ history, ∀ x y : ↥(↑S : Set W),
    f x = f y → (x.1 ∈ H ↔ y.1 ∈ H)

/-- Equality in a target witness remembers any requested finite list of
membership predicates after projection to D.  This is precisely the
root-isolation information needed by functional witness gluing. -/
def FunctionalRespectsProjectedHistory
    (p : W → P) (S : Finset W)
    (f : ↥(↑S : Set W) → Y)
    (history : List (Set P)) : Prop :=
  ∀ H ∈ history, ∀ x y : ↥(↑S : Set W),
    f x = f y → (p x.1 ∈ H ↔ p y.1 ∈ H)

/-- Generator-rank version of projected-history local tree completion.
Only genuine closed tested substructures occur. -/
def FunctionalProjectedHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ history : List (Set P),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory p S f history

namespace FunctionalRespectsProjectedHistory

/-- Projected history survives postcomposition by an injective target map. -/
theorem postcomp
    {p : W → P} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    {history : List (Set P)}
    (h : FunctionalRespectsProjectedHistory p S f history)
    {Z : Type v} {T' : Structure L Z} (j : Embedding T T') :
    FunctionalRespectsProjectedHistory p S (j ∘ f) history := by
  intro H hH x y hxy
  exact h H hH x y (j.injective hxy)

end FunctionalRespectsProjectedHistory

namespace FunctionalRespectsSourceHistory

/-- Source history survives postcomposition by an injective target map. -/
theorem postcomp
    {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    {history : List (Set W)}
    (h : FunctionalRespectsSourceHistory S f history)
    {Z : Type v} {T' : Structure L Z} (j : Embedding T T') :
    FunctionalRespectsSourceHistory S (j ∘ f) history := by
  intro H hH x y hxy
  exact h H hH x y (j.injective hxy)

end FunctionalRespectsSourceHistory

namespace FunctionalProjectedPartialIntersections

/-- Projected-partial certificates survive postcomposition by a full target
embedding. -/
theorem postcomp
    {p : W → P} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (h : FunctionalProjectedPartialIntersections
      (A := A) (D := D) (C := C) (T := T) p S f)
    {Z : Type v} {T' : Structure L Z} (j : Embedding T T') :
    FunctionalProjectedPartialIntersections
      (A := A) (D := D) (C := C) (T := T') p S (j ∘ f) := by
  intro β H hH e hproj hRange
  obtain ⟨eHT, heHT, hcHT⟩ := h β H hH e hproj hRange
  refine ⟨j.comp eHT, ?_, hcHT.postcomp j⟩
  intro x
  change j (eHT x) = j (f ⟨e x, hRange x⟩)
  exact congrArg j (heHT x)

end FunctionalProjectedPartialIntersections

namespace FunctionalProjectedHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  intro S hS hgen history
  exact h S hS (hgen.mono hmn) history

/-- A witness whose kernel refines the part projection respects every finite
history list. -/
theorem respectsHistory_of_kernel_refines_projection
    {S : Finset W} {f : ↥(↑S : Set W) → Y}
    (hkern : ∀ x y : ↥(↑S : Set W),
      f x = f y → p x.1 = p y.1)
    (history : List (Set P)) :
    FunctionalRespectsProjectedHistory p S f history := by
  intro H _ x y hxy
  rw [hkern x y hxy]


/-- Pull a projected-history witness back along a full functional
homomorphism-embedding by passing to the closed projected image of the test.

Unlike the source-history pullback, no injectivity is required: all diary data
lives in the outer structure D and is therefore stable under quotienting the
test by the projection. -/
theorem witness_of_homEmbedding_image
    (hD : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := D) (Base := Base) id n)
    (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        IsHomomorphismEmbedding
          (C.induce (↑S : Set W) hS) Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory p S f history := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  let q : ↥(↑S : Set W) → P := p ∘ inc
  have hqIHE : IsHomomorphismEmbedding Small D q :=
    hp.comp inc.isHomomorphismEmbedding
  have hqHom : Small.IsHomomorphism D q := hqIHE.1

  let I : Finset P := S.image p
  have hrange : Set.range q = (↑I : Set P) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
      let xs : ↥(↑S : Set W) := ⟨x, hxS⟩
      exact ⟨xs, hxy⟩
  have hIclosed : D.IsClosed (↑I : Set P) := by
    rw [← hrange]
    exact hqHom.range_isClosed
  let R := D.induce (↑I : Set P) hIclosed
  let incR : Embedding R D :=
    inclusion D (↑I : Set P) hIclosed
  let qR : ↥(↑S : Set W) → ↥(↑I : Set P) :=
    fun x => ⟨q x, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩

  have hqRHom : Small.IsHomomorphism R qR :=
    hqHom.codRestrict (↑I : Set P) hIclosed
      (fun x => Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩)
  have hqRIHE : Small.IsHomomorphismEmbedding R qR := by
    refine ⟨hqRHom, ?_⟩
    intro X E hE e
    obtain ⟨g, hg⟩ := hqIHE.2 E hE e
    have hgrange :
        ∀ z : X, ∃ r : ↥(↑I : Set P), g z = incR r := by
      intro z
      let r : ↥(↑I : Set P) :=
        ⟨q (e z), Finset.mem_image.mpr
          ⟨(e z).1, (e z).2, rfl⟩⟩
      exact ⟨r, hg z⟩
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

  have hIgen : R.GeneratedByAtMost n := by
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

  obtain ⟨Z, Target, hTree, g, hg, hPartD, hHistD⟩ :=
    hD I hIclosed hIgen history
  let f : ↥(↑S : Set W) → Z := g ∘ qR
  have hf : Small.IsHomomorphismEmbedding Target f :=
    hg.comp hqRIHE

  have hPart :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := Target) p S f := by
    intro β H hH e hproj hRange
    let eD : Embedding (A.induce H hH) D :=
      β.comp (inclusion A H hH)
    have hRangeD : ∀ x, eD x ∈ I := by
      intro x
      apply Finset.mem_image.mpr
      refine ⟨e x, hRange x, ?_⟩
      change p (e x) = β x.1
      exact hproj x
    have hprojD : ∀ x, (id : P → P) (eD x) = β x.1 :=
      fun _ => rfl
    obtain ⟨eHT, heHT, hcHT⟩ :=
      hPartD β H hH eD hprojD hRangeD
    refine ⟨eHT, ?_, hcHT⟩
    intro x
    change eHT x = g (qR ⟨e x, hRange x⟩)
    have hx :
        (⟨eD x, hRangeD x⟩ : ↥(↑I : Set P)) =
          qR ⟨e x, hRange x⟩ := by
      apply Subtype.ext
      change β x.1 = p (e x)
      exact (hproj x).symm
    rw [← hx]
    exact heHT x

  have hHist :
      FunctionalRespectsProjectedHistory p S f history := by
    intro K hK x y hxy
    have hbase := hHistD K hK (qR x) (qR y) hxy
    change (p x.1 ∈ K ↔ p y.1 ∈ K) at hbase
    exact hbase

  exact ⟨Z, Target, hTree, f, hf, hPart, hHist⟩

/-- Projected-history coherence gives the literal closed-substructure
statement used in the manuscript.  A closed test on at most n vertices is
generated by all of its vertices, so its generator rank is at most n. -/
theorem toLocallyClosedTreeCompletable
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyClosedTreeCompletable Base C n := by
  intro S hScard hclosed
  let E := C.induce (↑S : Set W) hclosed
  letI : Fintype ↥(↑S : Set W) := Fintype.ofFinite _
  have hgen0 :
      E.GeneratedByAtMost (Fintype.card ↥(↑S : Set W)) :=
    generatedByAtMost_card E
  have hcard :
      Fintype.card ↥(↑S : Set W) = S.card := by
    simp
  have hgen : E.GeneratedByAtMost n := by
    apply hgen0.mono
    rw [hcard]
    exact hScard
  obtain ⟨Y, T, hTree, f, hf, _, _⟩ :=
    h S hclosed hgen []
  exact ⟨Y, T, hTree, f, hf⟩

/-- At identity projection, asking the history to remember every singleton
part of the tested closed set forces the witness map to be injective. -/
theorem injectiveWitness_identity
    {P : Type v} {D : Structure L P}
    {A : Structure L U} {Base : Structure L V}
    {n : ℕ}
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := D) (Base := Base) id n)
    (S : Finset P) (hS : D.IsClosed (↑S : Set P))
    (hgen : (D.induce (↑S : Set P) hS).GeneratedByAtMost n) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set P) → Z,
        (D.induce (↑S : Set P) hS).IsHomomorphismEmbedding Target f ∧
        Function.Injective f := by
  classical
  let history : List (Set P) :=
    S.toList.map (fun x => ({x} : Set P))
  obtain ⟨Z, Target, hTree, f, hf, _, hHist⟩ :=
    h S hS hgen history
  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro x y hxy
  let H : Set P := {x.1}
  have hxList : x.1 ∈ S.toList := by
    simpa using x.2
  have hH : H ∈ history := by
    simp [history, H, hxList]
  have hmem := hHist H hH x y hxy
  have hy : y.1 = x.1 := by
    have : y.1 ∈ H := hmem.mp (by simp [H])
    simpa [H] using this
  apply Subtype.ext
  exact hy.symm

end FunctionalProjectedHistoryTreeLike

/-- Source-history version of root isolation.  If the image of the source
root is recorded as one history subset, equality with a target-root point
forces the source point itself to lie in the source root.  This avoids any
assumption that the part projection is injective. -/
theorem rootIsolation_of_source_boundary
    {E H Z : Type v}
    {Esrc : Structure L E} {Dsrc : Structure L H}
    {Target : Structure L Z}
    (Boundary : Set E)
    (history : List (Set E))
    (hBoundary : Boundary ∈ history)
    (f : E → Z)
    (hHist :
      ∀ Hset ∈ history, ∀ x y : E,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset))
    (sD : Embedding Dsrc Esrc)
    (root : Embedding Dsrc Target)
    (q : H → H) (hq : Function.Surjective q)
    (hcompat : ∀ d, f (sD d) = root (q d))
    (hchar : ∀ x : E, x ∈ Boundary ↔
      ∃ d : H, x = sD d) :
    ∀ x d, f x = root d →
      ∃ d' : H, x = sD d' ∧ q d' = d := by
  intro x d hxd
  obtain ⟨d0, hd0⟩ := hq d
  have hEq : f x = f (sD d0) := by
    calc
      f x = root d := hxd
      _ = root (q d0) := congrArg root hd0.symm
      _ = f (sD d0) := (hcompat d0).symm
  have hxmem : x ∈ Boundary :=
    (hHist Boundary hBoundary x (sD d0) hEq).2
      ((hchar (sD d0)).2 ⟨d0, rfl⟩)
  obtain ⟨d', hx⟩ := (hchar x).1 hxmem
  refine ⟨d', hx, ?_⟩
  apply root.injective
  calc
    root (q d') = f (sD d') := (hcompat d').symm
    _ = f x := congrArg f hx.symm
    _ = root d := hxd

/-- Usable form of root isolation.  The side source is already the induced
closed test, so no closure proof appears in the statement. -/
theorem rootIsolation_of_recorded_boundary
    {E H Z : Type v}
    {Esrc : Structure L E} {Dsrc : Structure L H}
    {Target : Structure L Z}
    (pE : E → P)
    (Boundary : Set P)
    (history : List (Set P))
    (hBoundary : Boundary ∈ history)
    (f : E → Z)
    (hHist :
      ∀ Hset ∈ history, ∀ x y : E,
        f x = f y → (pE x ∈ Hset ↔ pE y ∈ Hset))
    (sD : Embedding Dsrc Esrc)
    (root : Embedding Dsrc Target)
    (hcompat : ∀ d, f (sD d) = root d)
    (hchar : ∀ x : E, pE x ∈ Boundary ↔
      ∃ d : H, x = sD d) :
    ∀ x d, f x = root d →
      ∃ d' : H, x = sD d' ∧ d' = d := by
  intro x d hxd
  have hEq : f x = f (sD d) := hxd.trans (hcompat d).symm
  have hmemRoot : pE (sD d) ∈ Boundary := by
    exact (hchar (sD d)).2 ⟨d, rfl⟩
  have hmemX : pE x ∈ Boundary :=
    (hHist Boundary hBoundary x (sD d) hEq).2 hmemRoot
  obtain ⟨d', hx⟩ := (hchar x).1 hmemX
  refine ⟨d', hx, ?_⟩
  apply root.injective
  calc
    root d' = f (sD d') := (hcompat d').symm
    _ = f x := congrArg f hx.symm
    _ = root d := hxd

/-- If a closed test is cut out from a full A-copy, its pullback subset of A
is closed. -/
theorem closedAmbientIntersection
    (α : Embedding A C)
    (S : Set W) (hS : C.IsClosed S) :
    A.IsClosed {a | α a ∈ S} :=
  closed_preimage α S hS


namespace FunctionalSourceHistoryGlue

variable {H E F Z₁ Z₂ C₀ : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C₀}
variable {TL : Structure L Z₁} {TR : Structure L Z₂}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Mixed full-function gluing from source-side history.

The only extra information beyond the relational proof is that equality in
each side witness remembers the source overlap itself.  This gives the
root-isolation condition needed for exact preservation of set-valued function
fibres. -/
theorem glue_recorded_source_boundary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTreeL : TreeAmalgam Base Z₁ TL)
    (hTreeR : TreeAmalgam Base Z₂ TR)
    (fL : E → Z₁) (fR : F → Z₂)
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (tL : Embedding Root TL) (tR : Embedding Root TR)
    (hcL : tL.ContainedInIrreducible)
    (hcR : tR.ContainedInIrreducible)
    (q : H → H) (hq : Function.Surjective q)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (BoundaryL : Set E) (BoundaryR : Set F)
    (histL : List (Set E)) (histR : List (Set F))
    (hBoundaryL : BoundaryL ∈ histL)
    (hBoundaryR : BoundaryR ∈ histR)
    (hHistL :
      ∀ Hset ∈ histL, ∀ x y : E,
        fL x = fL y → (x ∈ Hset ↔ y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ histR, ∀ x y : F,
        fR x = fR y → (x ∈ Hset ↔ y ∈ Hset))
    (hcharL : ∀ x : E, x ∈ BoundaryL ↔
      ∃ d : H, x = sL d)
    (hcharR : ∀ x : F, x ∈ BoundaryR ↔
      ∃ d : H, x = sR d) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C₀ → Z, Whole.IsHomomorphismEmbedding Target f := by
  have hrootL :
      IsFreeAmalgam.RootIsolated sL tL q fL := by
    intro x d hxd
    exact rootIsolation_of_source_boundary
      BoundaryL histL hBoundaryL fL hHistL
      sL tL q hq hcompatL hcharL x d hxd
  have hrootR :
      IsFreeAmalgam.RootIsolated sR tR q fR := by
    intro x d hxd
    exact rootIsolation_of_source_boundary
      BoundaryR histR hBoundaryR fR hHistR
      sR tR q hq hcompatR hcharR x d hxd
  exact
    LocallyClosedTreeCompletable.glueIsolatedRoot
      (Base := Base) hSrc hTreeL hTreeR hcL hcR
      q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR

end FunctionalSourceHistoryGlue

namespace FunctionalProjectedHistoryTreeLike

variable {H E F Z₁ Z₂ C₀ : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C₀}
variable {TL : Structure L Z₁} {TR : Structure L Z₂}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Mixed functional gluing from two projected-history witnesses.

The common source root is already a genuine closed substructure.  Its two
target embeddings are supplied by the projected-partial certificates and are
assumed contained in irreducibles.  A recorded boundary set characterizes the
source root on each side; this gives exactly the root-isolation hypotheses of
the full fibre-surjective functional glue. -/
theorem glue_recorded_boundary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTreeL : TreeAmalgam Base Z₁ TL)
    (hTreeR : TreeAmalgam Base Z₂ TR)
    (fL : E → Z₁) (fR : F → Z₂)
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (tL : Embedding Root TL) (tR : Embedding Root TR)
    (hcL : tL.ContainedInIrreducible)
    (hcR : tR.ContainedInIrreducible)
    (hcompatL : ∀ d, fL (sL d) = tL d)
    (hcompatR : ∀ d, fR (sR d) = tR d)
    (pL : E → P) (pR : F → P)
    (Boundary : Set P)
    (histL histR : List (Set P))
    (hBoundaryL : Boundary ∈ histL)
    (hBoundaryR : Boundary ∈ histR)
    (hHistL :
      ∀ Hset ∈ histL, ∀ x y : E,
        fL x = fL y → (pL x ∈ Hset ↔ pL y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ histR, ∀ x y : F,
        fR x = fR y → (pR x ∈ Hset ↔ pR y ∈ Hset))
    (hcharL : ∀ x : E, pL x ∈ Boundary ↔
      ∃ d : H, x = sL d)
    (hcharR : ∀ x : F, pR x ∈ Boundary ↔
      ∃ d : H, x = sR d) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : C₀ → Z, Whole.IsHomomorphismEmbedding Target f := by
  have hrootL :
      IsFreeAmalgam.RootIsolated sL tL id fL := by
    intro x d hxd
    obtain ⟨d', hx, hdd⟩ :=
      rootIsolation_of_recorded_boundary
        (pE := pL) Boundary histL hBoundaryL
        fL hHistL sL tL hcompatL hcharL x d hxd
    refine ⟨d', hx, ?_⟩
    simpa using hdd
  have hrootR :
      IsFreeAmalgam.RootIsolated sR tR id fR := by
    intro x d hxd
    obtain ⟨d', hx, hdd⟩ :=
      rootIsolation_of_recorded_boundary
        (pE := pR) Boundary histR hBoundaryR
        fR hHistR sR tR hcompatR hcharR x d hxd
    refine ⟨d', hx, ?_⟩
    simpa using hdd
  exact
    LocallyClosedTreeCompletable.glueIsolatedRoot
      (Base := Base) hSrc hTreeL hTreeR hcL hcR
      id fL fR
      (fun d => by simpa using hcompatL d)
      (fun d => by simpa using hcompatR d)
      hfL hfR hrootL hrootR

end FunctionalProjectedHistoryTreeLike


namespace FunctionalProjectedHistoryTreeLike

/-- Mixed glue specialized to the named full-function decomposition of a
closed attachment test.  The source is exactly the induced closed test. -/
theorem glue_closed_attachment_test
    {P0 V0 W0 I0 ZL ZR : Type v}
    {Bsys : Partite.System L.graph P0 V0}
    {Dsys : Partite.System L.graph P0 W0}
    {Supp : Set V0}
    {maps0 : I0 → _root_.StructuralRamsey.Partite.Closed.Embedding (Bsys.induce Supp) Dsys}
    {Test : Set (_root_.StructuralRamsey.Partite.Attachment.Vertex Supp (W := W0) (I := I0))}
    {idx : I0}
    {TL0 : Structure L ZL} {TR0 : Structure L ZR}
    (hSupp : RelStructure.FunctionClosedSet Bsys.toRelStructure Supp)
    (hTreeL : TreeAmalgam Base ZL TL0)
    (hTreeR : TreeAmalgam Base ZR TR0)
    (fL :
      _root_.StructuralRamsey.RelStructure.Attachment.PieceV
        Bsys.toRelStructure Supp Dsys.toRelStructure
        ((fun j => (maps0 j).1.toEmbedding)) Test idx → ZL)
    (fR :
      _root_.StructuralRamsey.RelStructure.Attachment.RestV
        (W := W0) (I := I0) Supp Test idx → ZR)
    (hfL :
      (_root_.StructuralRamsey.Partite.Closed.Attachment.FullPiece
        Bsys Supp Dsys maps0 Test idx).IsHomomorphismEmbedding TL0 fL)
    (hfR :
      (_root_.StructuralRamsey.Partite.Closed.Attachment.FullRest
        Bsys Supp Dsys maps0 Test idx).IsHomomorphismEmbedding TR0 fR)
    (rootL :
      Embedding
        (_root_.StructuralRamsey.Partite.Closed.Attachment.FullOverlap
          Bsys Supp Dsys maps0 Test idx)
        TL0)
    (rootR :
      Embedding
        (_root_.StructuralRamsey.Partite.Closed.Attachment.FullOverlap
          Bsys Supp Dsys maps0 Test idx)
        TR0)
    (hcL : rootL.ContainedInIrreducible)
    (hcR : rootR.ContainedInIrreducible)
    (hcompatL :
      ∀ d,
        fL (_root_.StructuralRamsey.Partite.Closed.Attachment.fullOverlapToPiece
          Bsys Supp Dsys maps0 Test idx hSupp d) = rootL d)
    (hcompatR :
      ∀ d,
        fR (_root_.StructuralRamsey.Partite.Closed.Attachment.fullOverlapToRest
          Bsys Supp Dsys maps0 Test idx hSupp d) = rootR d)
    (pL :
      _root_.StructuralRamsey.RelStructure.Attachment.PieceV
        Bsys.toRelStructure Supp Dsys.toRelStructure
        ((fun j => (maps0 j).1.toEmbedding)) Test idx → P)
    (pR :
      _root_.StructuralRamsey.RelStructure.Attachment.RestV
        (W := W0) (I := I0) Supp Test idx → P)
    (Boundary : Set P)
    (histL histR : List (Set P))
    (hBoundaryL : Boundary ∈ histL)
    (hBoundaryR : Boundary ∈ histR)
    (hHistL :
      ∀ Hset ∈ histL, ∀ x y,
        fL x = fL y → (pL x ∈ Hset ↔ pL y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ histR, ∀ x y,
        fR x = fR y → (pR x ∈ Hset ↔ pR y ∈ Hset))
    (hcharL :
      ∀ x, pL x ∈ Boundary ↔
        ∃ d, x =
          _root_.StructuralRamsey.Partite.Closed.Attachment.fullOverlapToPiece
            Bsys Supp Dsys maps0 Test idx hSupp d)
    (hcharR :
      ∀ x, pR x ∈ Boundary ↔
        ∃ d, x =
          _root_.StructuralRamsey.Partite.Closed.Attachment.fullOverlapToRest
            Bsys Supp Dsys maps0 Test idx hSupp d) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥Test → Z,
        (_root_.StructuralRamsey.Partite.Closed.Attachment.FullSmall
          Bsys Supp Dsys maps0 Test).IsHomomorphismEmbedding Target f := by
  let hfree :=
    _root_.StructuralRamsey.Partite.Closed.Attachment.full_decompose_named
      Bsys Supp Dsys maps0 Test idx hSupp
  exact glue_recorded_boundary
    (Base := Base)
    (hSrc := hfree)
    hTreeL hTreeR fL fR hfL hfR
    rootL rootR hcL hcR hcompatL hcompatR
    pL pR Boundary histL histR hBoundaryL hBoundaryR
    hHistL hHistR hcharL hcharR

end FunctionalProjectedHistoryTreeLike

end StructuralRamsey.Structure
