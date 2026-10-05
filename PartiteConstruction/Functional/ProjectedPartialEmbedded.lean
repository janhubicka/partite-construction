import PartiteConstruction.Functional.FreeAmalgamPullback

/-! # Projected partial certificates for arbitrary embedded A-substructures

The core projected-partial invariant is phrased using literal closed subsets
of A.  In mixed free-amalgam arguments the natural domains are canonically
isomorphic to such subsets rather than definitionally equal to them.  This
file packages the harmless change of presentation.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W Y X : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {T : Structure L Y}
variable {R : Structure L X}
variable {p : W → P} {S : Finset W}
variable {f : ↥(↑S : Set W) → Y}

namespace Embedding.ContainedInIrreducible

/-- Containment in an irreducible target piece is preserved by
precomposition of the source embedding. -/
theorem precomp
    {H Z : Type v} {E : Structure L H} {F : Structure L Z}
    {e : Embedding E T} (hc : e.ContainedInIrreducible)
    (j : Embedding F E) :
    (e.comp j).ContainedInIrreducible := by
  rcases hc with ⟨Q, I, hI, k, hk⟩
  refine ⟨Q, I, hI, k, ?_⟩
  intro x
  exact hk (j x)

end Embedding.ContainedInIrreducible


/-- Presentation-free form of projected partial A-intersection data.  It is
used internally by mixed free-amalgam gluing, where the natural partial
domains are pullbacks rather than literal subtype presentations. -/
def FunctionalProjectedEmbeddedIntersections
    {X0 : Type v} (R0 : Structure L X0)
    (p0 : X0 → P) {Y0 : Type v} (T0 : Structure L Y0)
    (f0 : X0 → Y0) : Prop :=
  ∀ {Q : Type v} (R : Structure L Q)
    (ell : Embedding R A) (β : Embedding A D)
    (e : Embedding R R0),
    (∀ x, p0 (e x) = β (ell x)) →
    ∃ eRT : Embedding R T0,
      (∀ x, eRT x = f0 (e x)) ∧
      eRT.ContainedInIrreducible

namespace FunctionalProjectedEmbeddedIntersections

/-- Presentation-free projected-intersection data survives target
postcomposition. -/
theorem postcomp
    {X0 Y0 Z0 : Type v}
    {R0 : Structure L X0} {T0 : Structure L Y0}
    {p0 : X0 → P} {f0 : X0 → Y0}
    (h : FunctionalProjectedEmbeddedIntersections
      (A := A) (D := D) R0 p0 T0 f0)
    {T1 : Structure L Z0} (j : Embedding T0 T1) :
    FunctionalProjectedEmbeddedIntersections
      (A := A) (D := D) R0 p0 T1 (j ∘ f0) := by
  intro Q R ell β e hproj
  obtain ⟨eRT, heRT, hc⟩ := h R ell β e hproj
  refine ⟨j.comp eRT, ?_, hc.postcomp j⟩
  intro x
  exact congrArg j (heRT x)

end FunctionalProjectedEmbeddedIntersections

namespace FunctionalProjectedPartialIntersections

/-- A projected-partial certificate applies to any full substructure already
embedded in A, not only to the literal induced presentation of its closed
range. -/
theorem embeddedWitness
    (h :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T) p S f)
    (β : Embedding A D)
    (ell : Embedding R A)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = β (ell x))
    (hRange : ∀ x, e x ∈ S) :
    ∃ eRT : Embedding R T,
      (∀ x, eRT x = f ⟨e x, hRange x⟩) ∧
      eRT.ContainedInIrreducible := by
  classical
  let H : Set U := Set.range ell
  have hH : A.IsClosed H := ell.range_isClosed
  let inc : Embedding (A.induce H hH) A :=
    inclusion A H hH
  have hToRange :
      ∀ x : X, ∃ z : H, ell x = inc z := by
    intro x
    exact ⟨⟨ell x, ⟨x, rfl⟩⟩, rfl⟩
  let toRange : Embedding R (A.induce H hH) :=
    ell.factorThroughClosedRange inc hToRange
  have hToRangeSpec (x : X) :
      inc (toRange x) = ell x := by
    have hx := Classical.choose_spec (hToRange x)
    exact hx.symm
  have hFromRange :
      ∀ z : H, ∃ x : X, inc z = ell x := by
    intro z
    rcases z.2 with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  let fromRange : Embedding (A.induce H hH) R :=
    inc.factorThroughClosedRange ell hFromRange
  have hFromRangeSpec (z : H) :
      ell (fromRange z) = inc z := by
    have hz := Classical.choose_spec (hFromRange z)
    exact hz.symm
  have hInv (x : X) : fromRange (toRange x) = x := by
    apply ell.injective
    calc
      ell (fromRange (toRange x)) = inc (toRange x) :=
        hFromRangeSpec (toRange x)
      _ = ell x := hToRangeSpec x
  let eH : Embedding (A.induce H hH) C :=
    e.comp fromRange
  have hprojH : ∀ z, p (eH z) = β z.1 := by
    intro z
    calc
      p (eH z) = β (ell (fromRange z)) :=
        hproj (fromRange z)
      _ = β z.1 := by
        apply congrArg β
        exact hFromRangeSpec z
  have hRangeH : ∀ z, eH z ∈ S := by
    intro z
    exact hRange (fromRange z)
  obtain ⟨eHT, heHT, hcHT⟩ :=
    h β H hH eH hprojH hRangeH
  let eRT : Embedding R T := eHT.comp toRange
  refine ⟨eRT, ?_, hcHT.precomp toRange⟩
  intro x
  change eHT (toRange x) = f ⟨e x, hRange x⟩
  calc
    eHT (toRange x) =
        f ⟨eH (toRange x), hRangeH (toRange x)⟩ :=
      heHT (toRange x)
    _ = f ⟨e x, hRange x⟩ := by
      apply congrArg f
      apply Subtype.ext
      change e (fromRange (toRange x)) = e x
      exact congrArg e (hInv x)


/-- A finite-test projected-partial certificate yields the presentation-free
certificate on the induced tested structure itself. -/
theorem toEmbeddedOnTest
    (hS : C.IsClosed (↑S : Set W))
    (h :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T) p S f) :
    let Small := C.induce (↑S : Set W) hS
    FunctionalProjectedEmbeddedIntersections
      (A := A) (D := D) Small (p ∘ Subtype.val) T f := by
  intro Small
  intro Q R ell β eSmall hproj
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  let eC : Embedding R C := inc.comp eSmall
  have hprojC : ∀ x, p (eC x) = β (ell x) := by
    intro x
    exact hproj x
  have hRange : ∀ x, eC x ∈ S := by
    intro x
    exact (eSmall x).2
  obtain ⟨eRT, heRT, hc⟩ :=
    h.embeddedWitness β ell eC hprojC hRange
  refine ⟨eRT, ?_, hc⟩
  intro x
  change eRT x = f (eSmall x)
  have hx := heRT x
  apply hx.trans
  apply congrArg f
  apply Subtype.ext
  rfl

end FunctionalProjectedPartialIntersections

end StructuralRamsey.Structure
