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
      (∀ x, p (e x) = β x.1) →
      (∀ x, e x ∈ S) →
      ∀ (ell : ↥H → U),
        (A.induce H).IsHomomorphismEmbedding A ell →
        ∃ (Z : Type v) (Target : RelStructure L Z),
          TreeAmalgam B Z Target ∧
          ∃ f : ↥(↑S : Set W) → Z,
            (C.induce (↑S : Set W)).IsHomomorphismEmbedding Target f ∧
            ProjectedPartialIntersections
              (A := A) (D := D) (C := C) (T := Target) p S f ∧
            RespectsProjectedHistory p S f history ∧
            ∃ targetCopy : Embedding A Target,
              ∀ x : ↥H,
                f ⟨e x, by assumption⟩ = targetCopy (ell x)

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
  intro S hS history β H e hproj hRange ell hell
  exact h.2 S (hS.trans hmn) history β H e
    hproj hRange ell hell

/-- The inclusion of an induced partial A-substructure is a valid identity
labelling request. -/
theorem identityLabel_isHomomorphismEmbedding
    (H : Set U) :
    (A.induce H).IsHomomorphismEmbedding A Subtype.val :=
  (inclusion A H).isHomomorphismEmbedding

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
  exact h.2 S hS history β H e hproj hRange Subtype.val
    (identityLabel_isHomomorphismEmbedding (A := A) H)

end ProjectedRelativeLabelledLocallyTreeLike
end StructuralRamsey.RelStructure
