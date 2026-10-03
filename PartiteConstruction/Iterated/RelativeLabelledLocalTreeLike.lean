import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Iterated.MixedCommonLabelGlue

/-! # Relative labelled local-tree completions

The hard mixed Picture step needs two side completions that agree on the
labels of their common projected A-boundary. Ordinary local tree-likeness
chooses the target A-copy independently on each side and does not provide
this relative extension property.

The invariant below keeps ordinary local tree-likeness and adds one
distinguished requirement: for a chosen full copy beta : A -> D and a chosen
subset H of A whose beta-image lies in the finite test, the witness may be
chosen so that those tested points are sent to a target A-copy with the
original labels a in H.

Calling the invariant twice with the same beta and H gives exactly the
common-label data needed by the checked common-label gluing theorem.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}
variable {A : RelStructure L U}
variable {B : RelStructure L V}
variable {D : RelStructure L P}

/-- Ordinary local tree-likeness plus a relative labelled extension
requirement for one distinguished partial A-boundary. -/
def RelativeLabelledLocallyTreeLike (n : ℕ) : Prop :=
  LocallyTreeLike A B D n ∧
  ∀ I : Finset P, I.card ≤ n →
    ∀ (β : Embedding A D) (H : Set U),
      ∀ hH : (∀ a : H, β a.1 ∈ I),
      ∃ (Y : Type v) (T : RelStructure L Y),
        TreeAmalgam B Y T ∧
        ∃ f : ↥(↑I : Set P) → Y,
          (D.induce (↑I : Set P)).IsHomomorphismEmbedding T f ∧
          (∀ γ : Embedding A D,
            ∃ γ' : Embedding A T,
              ∀ a : U, ∀ ha : γ a ∈ I,
                ∃ a' : U, f ⟨γ a, ha⟩ = γ' a') ∧
          ∃ target : Embedding A T,
            ∀ a : H, f ⟨β a.1, hH a⟩ = target a.1

namespace RelativeLabelledLocallyTreeLike

variable {m n : ℕ}

/-- Forget the relative extension datum. -/
theorem toLocallyTreeLike
    (h : RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n) :
    LocallyTreeLike A B D n :=
  h.1

/-- Monotonicity in the finite test bound. -/
theorem mono
    (h : RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n)
    (hmn : m ≤ n) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) m := by
  refine ⟨h.1.mono hmn, ?_⟩
  intro I hI β H hH
  exact h.2 I (hI.trans hmn) β H hH

/-- Level zero is relative-labelled whenever A embeds into B and B embeds
into D. The distinguished boundary is necessarily empty. -/
theorem zero_of_embeddings
    (eAB : Embedding A B) (jBD : Embedding B D) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) 0 := by
  refine ⟨LocallyTreeLike.zero_of_embeddings eAB jBD, ?_⟩
  intro I hI β H hH
  obtain ⟨Y, T, hTree, f, hf, hctrl⟩ :=
    LocallyTreeLike.zero_of_embeddings eAB jBD I hI
  refine ⟨Y, T, hTree, f, hf, hctrl, eAB, ?_⟩
  intro a
  have hEmpty : I = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hI)
  have ha := hH a
  rw [hEmpty] at ha
  exact (Finset.notMem_empty _ ha).elim

/-- If D homomorphism-embeds into irreducible A and A embeds into B, one
copy of B supplies the relative labelled property at every scale. -/
theorem of_homEmbedding_to_control
    (hA : A.Irreducible) (eAB : Embedding A B)
    (p : P → U) (hp : D.IsHomomorphismEmbedding A p)
    (n : ℕ) :
    RelativeLabelledLocallyTreeLike
      (A := A) (B := B) (D := D) n := by
  refine ⟨LocallyTreeLike.of_homEmbedding_to_base hA eAB p hp n, ?_⟩
  intro I hI β H hH
  let f : ↥(↑I : Set P) → V := fun x => eAB (p x.1)
  have hIncl :
      (D.induce (↑I : Set P)).IsHomomorphismEmbedding D Subtype.val :=
    (inclusion D (↑I : Set P)).isHomomorphismEmbedding
  have hRestrict :
      (D.induce (↑I : Set P)).IsHomomorphismEmbedding A
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hf :
      (D.induce (↑I : Set P)).IsHomomorphismEmbedding B f := by
    change (D.induce (↑I : Set P)).IsHomomorphismEmbedding B
      (eAB ∘ (p ∘ Subtype.val))
    exact eAB.isHomomorphismEmbedding.comp hRestrict
  have hctrl :
      ∀ γ : Embedding A D,
        ∃ γ' : Embedding A B,
          ∀ a : U, ∀ ha : γ a ∈ I,
            ∃ a' : U, f ⟨γ a, ha⟩ = γ' a' := by
    intro γ
    obtain ⟨γA, hγA⟩ := hp.after_irreducible_embedding hA γ
    let γB : Embedding A B := eAB.comp γA
    refine ⟨γB, ?_⟩
    intro a ha
    refine ⟨a, ?_⟩
    change eAB (p (γ a)) = eAB (γA a)
    exact congrArg eAB (hγA a).symm
  obtain ⟨βA, hβA⟩ := hp.after_irreducible_embedding hA β
  let target : Embedding A B := eAB.comp βA
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B),
    f, hf, hctrl, target, ?_⟩
  intro a
  change eAB (p (β a.1)) = eAB (βA a.1)
  exact congrArg eAB (hβA a.1).symm

end RelativeLabelledLocallyTreeLike
end StructuralRamsey.RelStructure
