import PartiteConstruction.Functional.FreeAmalgamEmbeddedInduction
import PartiteConstruction.Functional.TreeExtensionAutoHistoryGlue

/-! # Induction for projected-history tree completions of full free amalgams

A finite full source inside a functional free amalgam can be completed by
induction on its cardinal if the pure-side tests have projected-history
completions and every genuinely mixed test admits compatible relative
completions over a common strict separator tree.

The smaller common, left and right tests are supplied to the mixed case
together with their recursive completion properties.  The final gluing
uses finite singleton projected histories internally, so compatibility
with a possibly noninjective separator quotient follows automatically.

Only the geometric mixed-separator lifting hypothesis is left explicit.
This theorem is a reduction to that hypothesis, not its proof.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {VB X P : Type v}

/-- Every finite projected diary has a full functional tree-completion
witness.  Unlike the stronger relative-history invariant this definition
does not prescribe a distinguished partial A-copy in the target. -/
def HasProjectedHistoryTreeCompletion
    (Base : Structure L VB) (C : Structure L X) (p : X → P) : Prop :=
  ∀ history : List (Set P),
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : X → Z,
        C.IsHomomorphismEmbedding Target f ∧
        (∀ K ∈ history, ∀ x y : X,
          f x = f y → (p x ∈ K ↔ p y ∈ K))

end StructuralRamsey.Structure


namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C VB P : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {Base : Structure L VB}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Placement-sensitive local tree completion for a full functional free
amalgam, reduced to one mixed-separator lifting clause.

The clause `hMixed` is supplied with all three strict cardinal induction
hypotheses.  It must actually construct a strict separator tree and the
two compatible relative side completions.  No assumption that independent
completions synchronize is made. -/
theorem finiteHistoryCompletion_of_relativeMixed
    [Fintype P] [Nonempty P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (p : C → P)
    (hPureL :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole),
        (∀ x : X, ∃ a : E, e x = iL a) →
        HasProjectedHistoryTreeCompletion Base D (p ∘ e))
    (hPureR :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole),
        (∀ x : X, ∃ b : F, e x = iR b) →
        HasProjectedHistoryTreeCompletion Base D (p ∘ e))
    (hMixed :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        HasProjectedHistoryTreeCompletion Base pb.common
          (p ∘ (e.comp (pb.leftIn.comp pb.toLeft))) →
        HasProjectedHistoryTreeCompletion Base pb.left
          (p ∘ (e.comp pb.leftIn)) →
        HasProjectedHistoryTreeCompletion Base pb.right
          (p ∘ (e.comp pb.rightIn)) →
        ∀ history : List (Set P),
          ∃ (G : Type v) (Start : Structure L G) (q : pb.Common → G),
            TreeAmalgam Base G Start ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toLeft q ((p ∘ e) ∘ pb.leftIn)
              (history ++ singletonProjectedHistory P) ∧
            HasTreeExtensionProjectedHistoryCompletion
              (Base := Base) (Start := Start)
              pb.toRight q ((p ∘ e) ∘ pb.rightIn)
              (history ++ singletonProjectedHistory P)) :
    ∀ {X : Type v} [Finite X]
      (D : Structure L X) (e : Embedding D Whole),
      HasProjectedHistoryTreeCompletion Base D (p ∘ e) := by
  let Q : ∀ {X : Type v},
      (D : Structure L X) → Embedding D Whole → Prop :=
    fun {_} D e => HasProjectedHistoryTreeCompletion Base D (p ∘ e)

  have hMixedQ :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        Q pb.common (e.comp (pb.leftIn.comp pb.toLeft)) →
        Q pb.left (e.comp pb.leftIn) →
        Q pb.right (e.comp pb.rightIn) →
        Q D e := by
    intro X _ D e pb hNotL hNotR hCommon hLeft hRight
    change HasProjectedHistoryTreeCompletion Base D (p ∘ e)
    intro history
    obtain ⟨G, Start, q, hStart, hL, hR⟩ :=
      hMixed D e pb hNotL hNotR hCommon hLeft hRight history
    obtain ⟨Z, Target, hExt, f, hf, _hcompat, _hroot, hHist⟩ :=
      LocallyClosedTreeCompletable.glueRelative_withAutomaticProjectedHistory
        (Base := Base) pb.free q (p ∘ e) history hL hR
    exact ⟨Z, Target, hExt.toTree hStart, f, hf, hHist⟩

  have hInd :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole),
        Q D e :=
    finite_embedded_induction hSrc Q
      (fun D e hRange => hPureL D e hRange)
      (fun D e hRange => hPureR D e hRange)
      hMixedQ

  intro X _ D e
  exact hInd D e

end StructuralRamsey.Structure.IsFreeAmalgam
