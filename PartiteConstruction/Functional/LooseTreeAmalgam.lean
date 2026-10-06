import PartiteConstruction.Functional.MixedOverlapExactness
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Loose tree amalgams for full function structures

If the survey's irreducible-containment condition on gluing roots is dropped,
finite EHN sources admit a very simple tree completion.  Decompose a reducible
source as a proper free amalgam, recursively embed the two proper sides, and
freely glue the target trees over the original common substructure.  Because
the recursive maps are genuine full embeddings, the common root is reflected
exactly and the compatible lift is again a full embedding.

Thus all synchronization and fibre-surjectivity issues disappear at the loose
level.  The remaining difficulty in functional sparsening is precisely the
strict root-containment requirement of the survey's TreeAmalgam.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U V W : Type v}

/-- Full function-language tree amalgams with unrestricted full gluing roots. -/
inductive LooseTreeAmalgam (Base : Structure L V) :
    (W : Type v) → Structure L W → Prop
  | copy {W : Type v} {T : Structure L W}
      (e : Embedding Base T) (hsurj : Function.Surjective e) :
      LooseTreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : Structure L W₁} {T₂ : Structure L W₂}
      {D : Structure L Z} {T : Structure L W}
      (h₁ : LooseTreeAmalgam Base W₁ T₁)
      (h₂ : LooseTreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      LooseTreeAmalgam Base W T

namespace LooseTreeAmalgam

/-- Every strict functional tree amalgam is loose. -/
theorem ofTree
    {Base : Structure L V} {T : Structure L W}
    (h : TreeAmalgam Base W T) :
    LooseTreeAmalgam Base W T := by
  induction h with
  | copy e hsurj =>
      exact .copy e hsurj
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact .glue ih₁ ih₂ f₁ f₂ i₁ i₂ hfree

end LooseTreeAmalgam

/-- A full structure embeds into a loose tree of copies of Base. -/
def HasInjectiveLooseTreeCompletion
    (Base : Structure L V) (C : Structure L W) : Prop :=
  ∃ (Y : Type v) (T : Structure L Y),
    LooseTreeAmalgam Base Y T ∧ Nonempty (Embedding C T)

/-- Every finite EHN source admits an injective full completion into a loose
tree of copies of Base, provided the EHN control structure embeds into Base. -/
theorem IsEHNHomomorphismEmbedding.hasInjectiveLooseTreeCompletion
    {A : Structure L U} {C : Structure L W}
    {p : W → U} [Finite W]
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (eAB : Embedding A (show Structure L V from ‹_›)) :
    HasInjectiveLooseTreeCompletion
      (show Structure L V from ‹_›) C := by
  classical
  let Base : Structure L V := (show Structure L V from ‹_›)
  let aux :
      ∀ n : ℕ, ∀ {X : Type v} [Fintype X],
        ∀ (E : Structure L X) (q : X → U),
          Fintype.card X = n →
          E.IsEHNHomomorphismEmbedding A q →
          HasInjectiveLooseTreeCompletion Base E := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X instX E q hcard hE
        by_cases hIrr : E.Irreducible
        · obtain ⟨g, hg⟩ :=
            hE.2 E hIrr (Embedding.id E)
          let f : Embedding E Base := eAB.comp g
          have hTree : LooseTreeAmalgam Base V Base :=
            LooseTreeAmalgam.copy (Embedding.id Base) (by
              intro b
              exact ⟨b, rfl⟩)
          exact ⟨V, Base, hTree, ⟨f⟩⟩
        · have hdec : Nonempty (ProperFreeDecomposition E) := by
            by_contra hn
            exact hIrr
              ((irreducible_iff_noProperFreeDecomposition E).mpr hn)
          rcases hdec with ⟨d⟩
          letI : Finite d.Left :=
            Finite.of_injective d.leftIn d.leftIn.injective
          letI : Finite d.Right :=
            Finite.of_injective d.rightIn d.rightIn.injective
          letI : Fintype d.Left := Fintype.ofFinite d.Left
          letI : Fintype d.Right := Fintype.ofFinite d.Right
          have hleftCard : Fintype.card d.Left < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.leftIn d.leftIn.injective d.leftProper
          have hrightCard : Fintype.card d.Right < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.rightIn d.rightIn.injective d.rightProper
          have hLeftEHN :
              d.left.IsEHNHomomorphismEmbedding A
                (q ∘ d.leftIn) := by
            exact hE.comp d.leftIn.isEHNHomomorphismEmbedding
          have hRightEHN :
              d.right.IsEHNHomomorphismEmbedding A
                (q ∘ d.rightIn) := by
            exact hE.comp d.rightIn.isEHNHomomorphismEmbedding
          obtain ⟨YL, TL, hTreeL, ⟨eL⟩⟩ :=
            ih (Fintype.card d.Left) hleftCard
              d.left (q ∘ d.leftIn) rfl hLeftEHN
          obtain ⟨YR, TR, hTreeR, ⟨eR⟩⟩ :=
            ih (Fintype.card d.Right) hrightCard
              d.right (q ∘ d.rightIn) rfl hRightEHN
          let tL : Embedding d.common TL := eL.comp d.toLeft
          let tR : Embedding d.common TR := eR.comp d.toRight
          let Target :=
            FreeAmalgam.amalgam d.common TL TR tL tR
          let jL :=
            FreeAmalgam.leftEmbedding d.common TL TR tL tR
          let jR :=
            FreeAmalgam.rightEmbedding d.common TL TR tL tR
          have hTgt : IsFreeAmalgam tL tR jL jR :=
            FreeAmalgam.isFreeAmalgam d.common TL TR tL tR
          have hrootL :
              IsFreeAmalgam.RootIsolated
                d.toLeft tL id eL := by
            intro x z hxz
            refine ⟨z, ?_, rfl⟩
            apply eL.injective
            exact hxz
          have hrootR :
              IsFreeAmalgam.RootIsolated
                d.toRight tR id eR := by
            intro x z hxz
            refine ⟨z, ?_, rfl⟩
            apply eR.injective
            exact hxz
          let e :
              Embedding E Target :=
            IsFreeAmalgam.functionalLiftEmbedding
              d.free hTgt id Function.injective_id
              eL eR
              (fun _ => rfl) (fun _ => rfl)
              hrootL hrootR
          have hTree :
              LooseTreeAmalgam Base
                (FreeAmalgam.Vertex d.common TL TR tL tR)
                Target :=
            LooseTreeAmalgam.glue
              hTreeL hTreeR tL tR jL jR hTgt
          exact ⟨_, Target, hTree, ⟨e⟩⟩
  letI : Fintype W := Fintype.ofFinite W
  exact aux (Fintype.card W) C p rfl hp

end StructuralRamsey.Structure
