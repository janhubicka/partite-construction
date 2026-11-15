import PartiteConstruction.Functional.TrackCDomainEmptyFaithfulNative
import PartiteConstruction.Functional.TrackECanonicalArrowEquivalence

/-!
# Track C: exact genuine Option(Set) Ramsey arrow in faithful native Dom/Empty

The English two-pass / second-native-B-cover proof must apply the
verified native sparsening theorem to a genuine partial original
Ramsey arrow. This is legitimate in the full rich language only
after a FULL embedding equivalence compatible with composition,
not merely a pointwise domain/value homomorphism correspondence.

The merged faithful Dom/Empty translation supplies full embeddings
in BOTH directions on the exact original vertex maps, including
none, some(empty), and some(nonempty set). This module builds their
equivalence and proves Ramsey arrow equivalence among ANY THREE
canonical genuine partial structures. No closure hull, extra
vertices, arity restriction, part homomorphism weakening or
unverified canonicality of an intermediate OLD Picture is used.

All part colours can be incorporated as original unary relations
before applying the same theorem. The arrow equivalence by itself
does NOT transport the original H class/strong amalgamation or
produce an admissible genuine partial native C0.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackECanonicalArrowEquivalence

universe u v
variable {L : Language.{u}} {V W X : Type v}

/-- Full-faithfulness of the faithful Dom/Empty native expansion:
precisely the SAME sets of full embeddings in both categories,
on the literal original vertex maps. -/
noncomputable def domainEmptyFullEmbeddingEquiv
    (A : PartialSetStructure L V)
    (B : PartialSetStructure L W) :
    Embedding A B ≃
      Structure.Embedding A.domainEmptyEncode B.domainEmptyEncode where
  toFun := Embedding.domainEmptyEncode
  invFun := Embedding.ofDomainEmptyEncode
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Structure.Embedding.ext
    intro x
    rfl

/-- Faithful expansion of full embeddings commutes with
composition on the EXACT original vertex map. -/
theorem Embedding.domainEmptyEncode_comp
    {A : PartialSetStructure L V}
    {B : PartialSetStructure L W}
    {C : PartialSetStructure L X}
    (g : Embedding B C) (e : Embedding A B) :
    (g.comp e).domainEmptyEncode =
      g.domainEmptyEncode.comp e.domainEmptyEncode := by
  apply Structure.Embedding.ext
  intro x
  rfl

/-- The original genuine partial FULL embedding Ramsey arrow
is equivalent to the full native functional Ramsey arrow
between the corresponding canonical Dom/Empty expansions,
including the source-defined-empty operation case.

No assumption that every arbitrary native structure is legal:
all three objects here are canonical faithful encodings.
All colours and A/B-copy embeddings are transferred by
the exact same vertex maps. -/
theorem arrow_iff_canonicalDomainEmpty
    (A : PartialSetStructure L V)
    (B : PartialSetStructure L W)
    (C : PartialSetStructure L X)
    (κ : Type*) :
    Structure.Arrow
      A.domainEmptyEncode B.domainEmptyEncode
      C.domainEmptyEncode κ ↔
    GenuinePartialArrow A B C κ := by
  let ΦAB := (domainEmptyFullEmbeddingEquiv A B).symm
  let ΦBC := (domainEmptyFullEmbeddingEquiv B C).symm
  let ΦAC := (domainEmptyFullEmbeddingEquiv A C).symm
  have hNat
      (g : Structure.Embedding B.domainEmptyEncode C.domainEmptyEncode)
      (e : Structure.Embedding A.domainEmptyEncode B.domainEmptyEncode) :
      ΦAC (g.comp e) = (ΦBC g).comp (ΦAB e) := by
    apply Embedding.ext
    intro x
    rfl
  constructor
  · intro hArrow χ
    obtain ⟨b, hb⟩ := hArrow (fun a => χ (ΦAC a))
    refine ⟨ΦBC b, ?_⟩
    intro a₁ a₂
    let a₁' : Structure.Embedding
        A.domainEmptyEncode B.domainEmptyEncode := ΦAB.symm a₁
    let a₂' : Structure.Embedding
        A.domainEmptyEncode B.domainEmptyEncode := ΦAB.symm a₂
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
    let g : Structure.Embedding
        B.domainEmptyEncode C.domainEmptyEncode := ΦBC.symm b
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hg : ΦBC g = b := ΦBC.apply_symm_apply b
    have hNat' (a : Structure.Embedding
        A.domainEmptyEncode B.domainEmptyEncode) :
        ΦAC (g.comp a) = b.comp (ΦAB a) := by
      rw [← hg]
      exact hNat g a
    have hReflect (a : Structure.Embedding
        A.domainEmptyEncode B.domainEmptyEncode) :
        ΦAC.symm (b.comp (ΦAB a)) = g.comp a := by
      apply ΦAC.injective
      simpa only [ΦAC.apply_symm_apply] using (hNat' a).symm
    calc
      χ (g.comp a₁) =
          χ (ΦAC.symm (b.comp (ΦAB a₁))) :=
        congrArg χ (hReflect a₁).symm
      _ = χ (ΦAC.symm (b.comp (ΦAB a₂))) :=
        hb (ΦAB a₁) (ΦAB a₂)
      _ = χ (g.comp a₂) :=
        congrArg χ (hReflect a₂)

end StructuralRamsey.PartialSetStructure
