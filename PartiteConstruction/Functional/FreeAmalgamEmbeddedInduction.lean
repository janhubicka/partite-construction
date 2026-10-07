import PartiteConstruction.Functional.FreeAmalgamPullback

/-! # Finite induction inside a full functional free amalgam

A full embedding of a finite test into a functional free amalgam either
factors through a single side, or meets both sides genuinely.  In the latter
case the canonical pullback provides full (closed) source substructures for
the left, right and common parts.  All three are strictly smaller than the
tested source.

This is a well-founded induction principle for statements depending on the
*embedded test*, not merely on its isomorphism type.  In particular a future
relative-tree invariant can request witnesses with roots and histories
determined by the placement of the test in the ambient attachment.

The mixed-case hypothesis is kept explicit: finite size decrease does not
itself construct compatible tree completions of a reducible separator.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Well-founded induction on the cardinal of a finite full source embedded
in one fixed free amalgam.  In a mixed case the induction hypotheses cover
the two full side preimages and their common closed substructure.

The predicate may refer to the ambient embedding, allowing histories and
partial boundaries to be pulled back exactly. -/
theorem finite_embedded_induction
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (Q : ∀ {X : Type v},
      (D : Structure L X) → Embedding D Whole → Prop)
    (hPureL :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole),
        (∀ x : X, ∃ a : E, e x = iL a) →
        Q D e)
    (hPureR :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole),
        (∀ x : X, ∃ b : F, e x = iR b) →
        Q D e)
    (hMixed :
      ∀ {X : Type v} [Finite X]
        (D : Structure L X) (e : Embedding D Whole)
        (pb : EmbeddingPullback hSrc e),
        (¬ ∀ x : X, ∃ a : E, e x = iL a) →
        (¬ ∀ x : X, ∃ b : F, e x = iR b) →
        Q pb.common (e.comp (pb.leftIn.comp pb.toLeft)) →
        Q pb.left (e.comp pb.leftIn) →
        Q pb.right (e.comp pb.rightIn) →
        Q D e) :
    ∀ {X : Type v} [Finite X]
      (D : Structure L X) (e : Embedding D Whole),
      Q D e := by
  classical
  let aux :
      ∀ n : ℕ, ∀ {X : Type v} [Fintype X]
        (D : Structure L X) (e : Embedding D Whole),
        Fintype.card X = n → Q D e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X instX D e hcard
        by_cases hpureL : ∀ x : X, ∃ a : E, e x = iL a
        · exact hPureL D e hpureL
        by_cases hpureR : ∀ x : X, ∃ b : F, e x = iR b
        · exact hPureR D e hpureR
        let pb := hSrc.embeddingPullback e
        letI : Finite pb.Left :=
          Finite.of_injective pb.leftIn pb.leftIn.injective
        letI : Finite pb.Right :=
          Finite.of_injective pb.rightIn pb.rightIn.injective
        letI : Finite pb.Common :=
          Finite.of_injective pb.toLeft pb.toLeft.injective
        letI : Fintype pb.Left := Fintype.ofFinite pb.Left
        letI : Fintype pb.Right := Fintype.ofFinite pb.Right
        letI : Fintype pb.Common := Fintype.ofFinite pb.Common

        have hnotSurjL : ¬ Function.Surjective pb.leftIn := by
          intro hsurj
          apply hpureL
          intro x
          obtain ⟨a, hxa⟩ := hsurj x
          refine ⟨pb.leftMap a, ?_⟩
          calc
            e x = e (pb.leftIn a) := congrArg e hxa.symm
            _ = iL (pb.leftMap a) := pb.left_factor a

        have hnotSurjR : ¬ Function.Surjective pb.rightIn := by
          intro hsurj
          apply hpureR
          intro x
          obtain ⟨b, hxb⟩ := hsurj x
          refine ⟨pb.rightMap b, ?_⟩
          calc
            e x = e (pb.rightIn b) := congrArg e hxb.symm
            _ = iR (pb.rightMap b) := pb.right_factor b

        have hLeftCard : Fintype.card pb.Left < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_not_surjective
            pb.leftIn pb.leftIn.injective hnotSurjL

        have hRightCard : Fintype.card pb.Right < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_not_surjective
            pb.rightIn pb.rightIn.injective hnotSurjR

        have hCommonCard : Fintype.card pb.Common < n := by
          calc
            Fintype.card pb.Common ≤ Fintype.card pb.Left :=
              Fintype.card_le_of_injective
                pb.toLeft pb.toLeft.injective
            _ < n := hLeftCard

        have hCommon :
            Q pb.common (e.comp (pb.leftIn.comp pb.toLeft)) :=
          ih (Fintype.card pb.Common) hCommonCard
            pb.common (e.comp (pb.leftIn.comp pb.toLeft)) rfl
        have hLeft :
            Q pb.left (e.comp pb.leftIn) :=
          ih (Fintype.card pb.Left) hLeftCard
            pb.left (e.comp pb.leftIn) rfl
        have hRight :
            Q pb.right (e.comp pb.rightIn) :=
          ih (Fintype.card pb.Right) hRightCard
            pb.right (e.comp pb.rightIn) rfl

        exact hMixed D e pb hpureL hpureR hCommon hLeft hRight

  intro X _ D e
  letI : Fintype X := Fintype.ofFinite X
  exact aux (Fintype.card X) D e rfl

end StructuralRamsey.Structure.IsFreeAmalgam
