import PartiteConstruction.Functional.HistoryTreeCompletion

/-! # Relative-labelled functional history witnesses

The hard mixed step for set-valued functions needs the two side completions to
realize the common closed A-boundary with the same A-labels.  The ordinary
combined history invariant already embeds every projected closed partial
A-copy into an irreducible piece of the target tree.  One fresh copy of the
base, attached over that embedded partial copy, upgrades this to a prescribed
relative labelling without changing any of the diary or projected-partial
data.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W V : Type v}
variable {A : Structure L U} {D : Structure L P}
variable {C : Structure L W} {Base : Structure L V}

/-- Combined functional histories with one prescribed relative labelling of a
closed projected partial A-copy. -/
def FunctionalRelativeHistoryTreeLike
    (p : W → P) (n : ℕ) : Prop :=
  FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n ∧
  ∀ (S : Finset W) (hS : C.IsClosed (↑S : Set W)),
    (C.induce (↑S : Set W) hS).GeneratedByAtMost n →
    ∀ (projectedHistory : List (Set P))
      (sourceHistory : List (Set W))
      (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
      (e : Embedding (A.induce H hH) C)
      (hproj : ∀ x, p (e x) = β x.1)
      (hRange : ∀ x, e x ∈ S)
      (ell : Embedding (A.induce H hH) A),
      ∃ (Z : Type v) (Target : Structure L Z),
        TreeAmalgam Base Z Target ∧
        ∃ f : ↥(↑S : Set W) → Z,
          (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
          FunctionalProjectedPartialIntersections
            (A := A) (D := D) (C := C) (T := Target) p S f ∧
          FunctionalRespectsProjectedHistory
            p S f projectedHistory ∧
          FunctionalRespectsSourceHistory
            S f sourceHistory ∧
          ∃ targetCopy : Embedding A Target,
            ∀ x : ↥H,
              f ⟨e x, hRange x⟩ = targetCopy (ell x)

namespace FunctionalRelativeHistoryTreeLike

variable {p : W → P} {m n : ℕ}

/-- Forget the distinguished relative-labelling request. -/
theorem toHistory
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n :=
  h.1

/-- Monotonicity in generator rank. -/
theorem mono
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (hmn : m ≤ n) :
    FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p m := by
  refine ⟨h.1.mono hmn, ?_⟩
  intro S hS hgen projectedHistory sourceHistory β H hH e hproj hRange ell
  exact h.2 S hS (hgen.mono hmn) projectedHistory sourceHistory
    β H hH e hproj hRange ell

/-- Inclusion of a closed partial A-substructure gives the identity
relative-labelling request. -/
def identityLabelEmbedding
    (H : Set U) (hH : A.IsClosed H) :
    Embedding (A.induce H hH) A :=
  inclusion A H hH

/-- Specialize the relative request to identity A-labels. -/
theorem witness_identityLabels
    (h : FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hgen : (C.induce (↑S : Set W) hS).GeneratedByAtMost n)
    (projectedHistory : List (Set P))
    (sourceHistory : List (Set W))
    (β : Embedding A D) (H : Set U) (hH : A.IsClosed H)
    (e : Embedding (A.induce H hH) C)
    (hproj : ∀ x, p (e x) = β x.1)
    (hRange : ∀ x, e x ∈ S) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding Target f ∧
        FunctionalProjectedPartialIntersections
          (A := A) (D := D) (C := C) (T := Target) p S f ∧
        FunctionalRespectsProjectedHistory
          p S f projectedHistory ∧
        FunctionalRespectsSourceHistory
          S f sourceHistory ∧
        ∃ targetCopy : Embedding A Target,
          ∀ x : ↥H,
            f ⟨e x, hRange x⟩ = targetCopy x.1 := by
  obtain ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, htarget⟩ :=
    h.2 S hS hgen projectedHistory sourceHistory
      β H hH e hproj hRange (identityLabelEmbedding (A := A) H hH)
  refine ⟨Z, Target, hTree, f, hf, hPart, hProj, hSrc,
    targetCopy, ?_⟩
  intro x
  simpa [identityLabelEmbedding] using htarget x

/-- The relative request is automatic from the ordinary combined history
invariant: attach one fresh copy of Base over the already embedded partial
A-boundary. -/
theorem ofHistory
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    (h : FunctionalHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n) :
    FunctionalRelativeHistoryTreeLike
      (A := A) (D := D) (C := C) (Base := Base) p n := by
  classical
  refine ⟨h, ?_⟩
  intro S hS hgen projectedHistory sourceHistory
    β H hH e hproj hRange ell
  obtain ⟨Y, T, hTree, f, hf, hPart, hProj, hSrc⟩ :=
    h S hS hgen projectedHistory sourceHistory
  obtain ⟨eHT, heHT, hcT⟩ :=
    hPart β H hH e hproj hRange
  let Hstr := A.induce H hH
  let eHB : Embedding Hstr Base :=
    eAB.comp ell
  have hcB : eHB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro x
    exact ⟨ell x, rfl⟩
  let T' := FreeAmalgam.amalgam Hstr T Base eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding Hstr T Base eHT eHB
  let r : Embedding Base T' :=
    FreeAmalgam.rightEmbedding Hstr T Base eHT eHB
  have hfree : IsFreeAmalgam eHT eHB l r :=
    FreeAmalgam.isFreeAmalgam Hstr T Base eHT eHB
  have hTree' : TreeAmalgam Base _ T' :=
    FreeAmalgam.treeAmalgam Hstr T Base eHT eHB Base
      hTree
      (TreeAmalgam.copy (Embedding.id Base) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB
  let f' : ↥(↑S : Set W) → _ := l ∘ f
  have hf' :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T' f' :=
    l.isHomomorphismEmbedding.comp hf
  have hPart' :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := T') p S f' :=
    hPart.postcomp l
  have hProj' :
      FunctionalRespectsProjectedHistory p S f' projectedHistory :=
    hProj.postcomp l
  have hSrc' :
      FunctionalRespectsSourceHistory S f' sourceHistory :=
    hSrc.postcomp l
  let targetCopy : Embedding A T' := r.comp eAB
  refine ⟨_, T', hTree', f', hf', hPart', hProj', hSrc',
    targetCopy, ?_⟩
  intro x
  change l (f ⟨e x, hRange x⟩) = r (eAB (ell x))
  calc
    l (f ⟨e x, hRange x⟩) = l (eHT x) :=
      congrArg l (heHT x).symm
    _ = r (eHB x) :=
      (hfree.overlap (eHT x) (eHB x)).mpr ⟨x, rfl, rfl⟩
    _ = r (eAB (ell x)) := rfl

end FunctionalRelativeHistoryTreeLike

end StructuralRamsey.Structure
