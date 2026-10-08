import PartiteConstruction.Ramsey.CompletionTransfer

/-! # Copywise completions through a free source amalgam

The target amalgam in a multiamalgamation class is *not* free: it may
add relations between the two sides. The correct completion map from a
free source amalgam is defined using the source covering property only.

Its restrictions to B-copies are embeddings whenever the corresponding
side maps are B-copywise completions. This requires irreducibility of B
to localize a B-copy to one side, but neither injectivity nor even a
global homomorphism property of the resulting completion map.

In particular, this lemma does not assume that the target belongs to
a free-amalgamation class.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C P X Y Z : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

namespace IsFreeAmalgam

/-- Fold maps of the two sources that agree on the common root, without
requiring any free amalgam or even a relational structure on the target. -/
noncomputable def compatibleFold
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d, fL (sL d) = fR (sR d)) : C → X := by
  classical
  intro x
  exact if h : ∃ a : E, x = iL a then
      fL (Classical.choose h)
    else
      fR (Classical.choose ((hSrc.covers x).resolve_left h))

theorem compatibleFold_left
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d, fL (sL d) = fR (sR d))
    (a : E) :
    compatibleFold hSrc fL fR hcompat (iL a) = fL a := by
  classical
  unfold compatibleFold
  have h : ∃ b : E, iL a = iL b := ⟨a, rfl⟩
  rw [dif_pos h]
  have heq : a = Classical.choose h :=
    iL.injective (Classical.choose_spec h)
  exact congrArg fL heq.symm

theorem compatibleFold_right
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d, fL (sL d) = fR (sR d))
    (b : F) :
    compatibleFold hSrc fL fR hcompat (iR b) = fR b := by
  classical
  by_cases h : ∃ a : E, iR b = iL a
  · unfold compatibleFold
    rw [dif_pos h]
    have hroot : iL (Classical.choose h) = iR b :=
      (Classical.choose_spec h).symm
    obtain ⟨d, hdL, hdR⟩ :=
      (hSrc.overlap (Classical.choose h) b).mp hroot
    calc
      fL (Classical.choose h) = fL (sL d) :=
        congrArg fL hdL
      _ = fR (sR d) := hcompat d
      _ = fR b := congrArg fR hdR.symm
  · unfold compatibleFold
    rw [dif_neg h]
    let hb : ∃ c : F, iR b = iR c :=
      (hSrc.covers (iR b)).resolve_left h
    change fR (Classical.choose hb) = fR b
    have heq : Classical.choose hb = b :=
      iR.injective (Classical.choose_spec hb).symm
    exact congrArg fR heq

end IsFreeAmalgam

namespace CopywiseCompletion

/-- Copywise target completions of both sides glue across a *free source*
amalgam into an arbitrary target, provided their two target embeddings
agree on the common source root. The resulting map is not asserted to be
a global homomorphism or embedding. -/
theorem fold_free
    {Base : RelStructure L P}
    (hBase : Base.Irreducible)
    (hSrc : IsFreeAmalgam sL sR iL iR)
    {TL : RelStructure L X} {TR : RelStructure L Y}
    {Target : RelStructure L Z}
    (fL : E → X) (fR : F → Y)
    (hL : CopywiseCompletion Base Left TL fL)
    (hR : CopywiseCompletion Base Right TR fR)
    (jL : Embedding TL Target) (jR : Embedding TR Target)
    (hcompat : ∀ d, jL (fL (sL d)) = jR (fR (sR d))) :
    CopywiseCompletion Base Whole Target
      (hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR) hcompat) := by
  classical
  intro e
  let S : Set C := Set.range e
  have hS : (Whole.induce S).Irreducible :=
    hBase.range_embedding e
  rcases hSrc.irreducible_side S hS with hLeft | hRight
  · have hrange : ∀ x : P, ∃ a : E, e x = iL a := by
      intro x
      exact hLeft ⟨e x, ⟨x, rfl⟩⟩
    let eL : Embedding Base Left :=
      e.factorThroughRange iL hrange
    obtain ⟨g, hg⟩ := hL eL
    refine ⟨jL.comp g, ?_⟩
    intro x
    calc
      (jL.comp g) x = jL (g x) := rfl
      _ = jL (fL (eL x)) := congrArg jL (hg x)
      _ = hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR)
            hcompat (iL (eL x)) :=
        (hSrc.compatibleFold_left (jL ∘ fL) (jR ∘ fR) hcompat (eL x)).symm
      _ = hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR)
            hcompat (e x) := by
        exact congrArg
          (hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR) hcompat)
          (Classical.choose_spec (hrange x)).symm
  · have hrange : ∀ x : P, ∃ b : F, e x = iR b := by
      intro x
      exact hRight ⟨e x, ⟨x, rfl⟩⟩
    let eR : Embedding Base Right :=
      e.factorThroughRange iR hrange
    obtain ⟨g, hg⟩ := hR eR
    refine ⟨jR.comp g, ?_⟩
    intro x
    calc
      (jR.comp g) x = jR (g x) := rfl
      _ = jR (fR (eR x)) := congrArg jR (hg x)
      _ = hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR)
            hcompat (iR (eR x)) :=
        (hSrc.compatibleFold_right (jL ∘ fL) (jR ∘ fR) hcompat (eR x)).symm
      _ = hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR)
            hcompat (e x) := by
        exact congrArg
          (hSrc.compatibleFold (jL ∘ fL) (jR ∘ fR) hcompat)
          (Classical.choose_spec (hrange x)).symm

end CopywiseCompletion

end StructuralRamsey.RelStructure
