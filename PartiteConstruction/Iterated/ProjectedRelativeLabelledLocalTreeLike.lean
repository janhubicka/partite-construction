import PartiteConstruction.Iterated.ProjectedHistoryLocalTreeLike

/-! # Projected relative labelled witnesses

The mixed Picture step needs side completions that realize a prescribed common
labelling on a reducible projected overlap. Identity labels are enough for
that one step, but they are not stable under pure-core/pure-copy
reparametrization.

The invariant below therefore allows the requested partial A-boundary to be
relabelled by an arbitrary homomorphism-embedding into A. It also carries the
existing projected-partial and finite-history data in the same witness.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P W : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}
variable {C : RelStructure L W}

/-- Projected history witnesses with one prescribed relative labelled partial
A-boundary. -/
def ProjectedRelativeLabelledLocallyTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n ∧
  ∀ S : Finset W, S.card ≤ n →
    ∀ history : List (Set P),
    ∀ (β : Embedding A D) (H : Set U)
      (e : Embedding (A.induce H) C),
      ∀ hproj : (∀ x, p (e x) = β x.1),
      ∀ hRange : (∀ x, e x ∈ S),
      ∀ (ell : Embedding (A.induce H) A),
        ∃ (Z : Type v) (Target : RelStructure L Z),
          TreeAmalgam B Z Target ∧
          ∃ f : ↥(↑S : Set W) → Z,
            (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
            ProjectedPartialIntersections
              (A := A) (D := D) (C := C) (T := Target) p S f ∧
            RespectsProjectedHistory p S f history ∧
            ∃ targetCopy : Embedding A Target,
              ∀ x : ↥H,
                f ⟨e x, hRange x⟩ = targetCopy (ell x)

namespace ProjectedRelativeLabelledLocallyTreeLike

variable {p : W → P}
variable {m n : ℕ}

/-- Forget the relative request. -/
theorem toProjectedHistory
    (h : ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n) :
    ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n :=
  h.1

/-- Monotonicity in the test-size parameter. -/
theorem mono
    (h : ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n)
    (hmn : m ≤ n) :
    ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p m := by
  refine ⟨h.1.mono hmn, ?_⟩
  intro S hS history β H e hproj hRange ell
  exact h.2 S (hS.trans hmn) history β H e
    hproj hRange ell

/-- The inclusion of an induced partial A-substructure is the identity
labelling request. -/
def identityLabelEmbedding
    (H : Set U) : Embedding (A.induce H) A :=
  inclusion A H

/-- Specialize the relative request to identity labels. -/
theorem witness_identityLabels
    (h : ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n)
    (S : Finset W) (hS : S.card ≤ n)
    (history : List (Set P))
    (β : Embedding A D) (H : Set U)
    (e : Embedding (A.induce H) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S) :
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
        ProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        RespectsProjectedHistory p S f history ∧
        ∃ targetCopy : Embedding A Target,
          ∀ x : ↥H, f ⟨e x, hRange x⟩ = targetCopy x.1 := by
  exact h.2 S hS history β H e hproj hRange
    (identityLabelEmbedding (A := A) H)


/-- Projected partial-intersection data survives postcomposition of the target
by an induced embedding. -/
theorem ProjectedPartialIntersections.postcomp
    {Y Z : Type v} {T : RelStructure L Y} {T' : RelStructure L Z}
    {S : Finset W} {f : ↥(↑S : Set W) → Y}
    (hPart : ProjectedPartialIntersections
      (A := A) (D := D) (C := C) (T := T) p S f)
    (j : Embedding T T') :
    ProjectedPartialIntersections
      (A := A) (D := D) (C := C) (T := T') p S (j ∘ f) := by
  intro β H e hproj hRange
  obtain ⟨eHT, heHT, hc⟩ := hPart β H e hproj hRange
  refine ⟨j.comp eHT, ?_, hc.postcomp j⟩
  intro x
  exact congrArg j (heHT x)

/-- Finite projected histories survive postcomposition by an embedding of the
target. -/
theorem RespectsProjectedHistory.postcomp
    {Y Z : Type v} {S : Finset W}
    {f : ↥(↑S : Set W) → Y}
    (hHist : RespectsProjectedHistory p S f
      ([] : List (Set P)))
    (j : Y → Z) (hj : Function.Injective j) :
    RespectsProjectedHistory p S (j ∘ f)
      ([] : List (Set P)) := by
  intro H hH
  simp at hH

/-- A single relative embedding request is automatic from the projected
history invariant: first take an ordinary projected-history witness, then
attach one fresh B-copy over the already embedded requested boundary.

The requested relabelling must be an induced embedding.  Allowing a
noninjective homomorphism-embedding would contradict the projected-partial
condition, which already makes the boundary map injective. -/
theorem ofProjectedHistory
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (h : ProjectedHistoryLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n) :
    ProjectedRelativeLabelledLocallyTreeLike
      (A := A) (D := D) (C := C) (B := B) p n := by
  classical
  refine ⟨h, ?_⟩
  intro S hS history β H e hproj hRange ell
  obtain ⟨Y, T, hTree, f, hf, hPart, hHist⟩ :=
    h S hS history
  obtain ⟨eHT, heHT, hcT⟩ :=
    hPart β H e hproj hRange
  let eHB : Embedding (A.induce H) B := eAB.comp ell
  have hcB : eHB.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA eAB eHB
    intro x
    exact ⟨ell x, rfl⟩
  let T' := FreeAmalgam.amalgam (A.induce H) T B eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding (A.induce H) T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding (A.induce H) T B eHT eHB
  have hTree' : TreeAmalgam B _ T' :=
    FreeAmalgam.treeAmalgam (A.induce H) T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  let f' : ↥(↑S : Set W) → _ := l ∘ f
  have hf' :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' :=
    l.isHomomorphismEmbedding.comp hf
  have hPart' :
      ProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T') p S f' := by
    intro β' H' e' hproj' hRange'
    obtain ⟨eHT', heHT', hcHT'⟩ :=
      hPart β' H' e' hproj' hRange'
    refine ⟨l.comp eHT', ?_, hcHT'.postcomp l⟩
    intro x
    exact congrArg l (heHT' x)
  have hHist' :
      RespectsProjectedHistory p S f' history := by
    intro K hK x y hxy
    apply hHist K hK x y
    apply l.injective
    exact hxy
  let targetCopy : Embedding A T' := r.comp eAB
  refine ⟨_, T', hTree', f', hf', hPart', hHist',
    targetCopy, ?_⟩
  intro x
  change l (f ⟨e x, hRange x⟩) =
    r (eAB (ell x))
  calc
    l (f ⟨e x, hRange x⟩) = l (eHT x) :=
      congrArg l (heHT x).symm
    _ = r (eHB x) :=
      FreeAmalgam.left_right_overlap
        (A.induce H) T B eHT eHB x
    _ = r (eAB (ell x)) := rfl

end ProjectedRelativeLabelledLocallyTreeLike
end StructuralRamsey.RelStructure
