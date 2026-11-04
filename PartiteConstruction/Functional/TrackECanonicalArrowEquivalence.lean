import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Appendix A Track E: full Ramsey arrows across faithful native/partial encodings

The previously audited full-embedding equivalence
`TrackENativePartialFullFaithfulness.nativePartialFullEmbeddingEquiv`
is literally identity-on-vertices, and hence is compatible with
composition. The present module turns this into an iff of actual
Ramsey arrows on the SAME three canonical native structures A, B, C.

The target C must itself be a faithful native encoding. This proof
does not imply that arbitrary intermediate 2019 profiled sparse
relational witnesses decode to native functions; the separate
defined-empty and coherence normality obligations remain.

No part-labelled output, generated hull, arity restriction,
finiteness or additional colours are assumed.
-/

namespace StructuralRamsey.Structure.TrackECanonicalArrowEquivalence

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v
variable {L : Language.{u}} {V W X : Type v}

/-- Ramsey arrow for genuine independent-domain Option(Set)
structures, using FULL embeddings on every A/B copy. Unlike an
arbitrary OLD relational homomorphism-embedding, neither domain
definedness nor any output value may change on a copy. -/
def GenuinePartialArrow
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (C : PartialSetStructure L X) (κ : Type*) : Prop :=
  ∀ χ : PartialSetStructure.Embedding A C → κ,
    ∃ b : PartialSetStructure.Embedding B C,
      ∀ a₁ a₂ : PartialSetStructure.Embedding A B,
        χ (b.comp a₁) = χ (b.comp a₂)

/-- Full native/partial embedding translation commutes with the
actual composition of copies. No artificial naturality axiom is
assumed: prove equality of full embeddings by vertex extensionality. -/
theorem toNonemptyPartial_comp
    {A : Structure L V} {B : Structure L W} {C : Structure L X}
    (g : Structure.Embedding B C) (e : Structure.Embedding A B) :
    (g.comp e).toNonemptyPartial =
      g.toNonemptyPartial.comp e.toNonemptyPartial := by
  apply PartialSetStructure.Embedding.ext
  intro x
  rfl

/-- The native full-function Ramsey arrow is equivalent to the
genuine partial-function Ramsey arrow for the canonical encodings
of the SAME A, B and C, for an arbitrary colour type κ.
The iff retains exactly the original vertex maps and all full
A/B embeddings, even when some native fibres are empty. -/
theorem arrow_iff_canonicalNonemptyPartial
    (A : Structure L V) (B : Structure L W)
    (C : Structure L X) (κ : Type*) :
    Structure.Arrow A B C κ ↔
      GenuinePartialArrow A.toNonemptyPartial
        B.toNonemptyPartial C.toNonemptyPartial κ := by
  let ΦAB := nativePartialFullEmbeddingEquiv A B
  let ΦBC := nativePartialFullEmbeddingEquiv B C
  let ΦAC := nativePartialFullEmbeddingEquiv A C
  have hNat (g : Structure.Embedding B C) (e : Structure.Embedding A B) :
      ΦAC (g.comp e) = (ΦBC g).comp (ΦAB e) := by
    apply PartialSetStructure.Embedding.ext
    intro x
    rfl
  constructor
  · intro hArrow χ
    obtain ⟨b, hb⟩ := hArrow (fun a => χ (ΦAC a))
    refine ⟨ΦBC b, ?_⟩
    intro a₁ a₂
    let a₁' : Structure.Embedding A B := ΦAB.symm a₁
    let a₂' : Structure.Embedding A B := ΦAB.symm a₂
    have ha₁ : ΦAB a₁' = a₁ := ΦAB.apply_symm_apply a₁
    have ha₂ : ΦAB a₂' = a₂ := ΦAB.apply_symm_apply a₂
    have hn₁ : ΦAC (b.comp a₁') = (ΦBC b).comp a₁ := by
      rw [← ha₁]
      exact hNat b a₁'
    have hn₂ : ΦAC (b.comp a₂') = (ΦBC b).comp a₂ := by
      rw [← ha₂]
      exact hNat b a₂'
    rw [← hn₁, ← hn₂]
    exact hb a₁' a₂'
  · intro hArrow χ
    obtain ⟨b, hb⟩ := hArrow (fun a => χ (ΦAC.symm a))
    let g : Structure.Embedding B C := ΦBC.symm b
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hg : ΦBC g = b := ΦBC.apply_symm_apply b
    have hNat' (a : Structure.Embedding A B) :
        ΦAC (g.comp a) = b.comp (ΦAB a) := by
      rw [← hg]
      exact hNat g a
    have hReflect (a : Structure.Embedding A B) :
        ΦAC.symm (b.comp (ΦAB a)) = g.comp a := by
      apply ΦAC.injective
      simpa only [ΦAC.apply_symm_apply] using (hNat' a).symm
    calc
      χ (g.comp a₁) =
          χ (ΦAC.symm (b.comp (ΦAB a₁))) := by
            exact congrArg χ (hReflect a₁).symm
      _ = χ (ΦAC.symm (b.comp (ΦAB a₂))) :=
            hb (ΦAB a₁) (ΦAB a₂)
      _ = χ (g.comp a₂) :=
            congrArg χ (hReflect a₂)

end StructuralRamsey.Structure.TrackECanonicalArrowEquivalence
