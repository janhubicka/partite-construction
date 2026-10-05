import PartiteConstruction.Functional.GeneratedTreeCompletion

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

namespace Embedding.ContainedInIrreducible

/-- Containment in an irreducible functional piece survives
postcomposition by a full embedding of the target. -/
theorem postcomp
    {H Z : Type v} {E : Structure L H}
    {e : Embedding E T} (hc : e.ContainedInIrreducible)
    {T' : Structure L Z} (j : Embedding T T') :
    (j.comp e).ContainedInIrreducible := by
  rcases hc with ⟨X, R, hR, k, hk⟩
  refine ⟨X, R, hR, j.comp k, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := hk a
  exact ⟨x, congrArg j hx⟩

end Embedding.ContainedInIrreducible

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


/-- Projected-history coherence immediately implies generator-local tree
completability by forgetting the extra partial-intersection and history data. -/
theorem toLocallyGeneratedTreeCompletable
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyGeneratedTreeCompletable Base C n := by
  intro Z _ E hgen e
  let R : Set W := Set.range e
  have hRclosed : C.IsClosed R := e.range_isClosed
  let S : Finset W := Finset.univ.image e
  have hSset : (↑S : Set W) = R := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨z, _, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hSclosed : C.IsClosed (↑S : Set W) := by
    rw [hSset]
    exact hRclosed
  let eR : Embedding E (C.induce (↑S : Set W) hSclosed) := by
    refine e.factorThroughRange
      (inclusion C (↑S : Set W) hSclosed) ?_
    intro z
    exact ⟨⟨e z, by
      change e z ∈ (↑S : Set W)
      exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩⟩, rfl⟩
  have hgenS :
      (C.induce (↑S : Set W) hSclosed).GeneratedByAtMost n := by
    have hhom :
        E.IsHomomorphism
          (C.induce (↑S : Set W) hSclosed) eR :=
      eR.isHomomorphism
    have hRangeAll :
        Set.range eR = Set.univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rcases x with ⟨w, hw⟩
        have hwR : w ∈ Set.range e := by
          rw [← hSset]
          exact hw
        rcases hwR with ⟨z, rfl⟩
        exact ⟨z, by
          apply Subtype.ext
          rfl⟩
    have hRgen :=
      homRange_generatedByAtMost hhom hgen
    simpa [hRangeAll] using hRgen
  obtain ⟨Y, T, hTree, f, hf, _, _⟩ :=
    h S hSclosed hgenS []
  exact ⟨Y, T, hTree, f ∘ eR, hf.comp eR.isHomomorphismEmbedding⟩

/-- In particular, projected-history coherence gives the literal
closed-substructure statement used in the manuscript. -/
theorem toLocallyClosedTreeCompletable
    (h : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    LocallyClosedTreeCompletable Base C n :=
  h.toLocallyGeneratedTreeCompletable.toLocallyClosedTreeCompletable

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

end StructuralRamsey.Structure
