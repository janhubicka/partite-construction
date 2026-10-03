import PartiteConstruction.Iterated.ProjectedRoot
import PartiteConstruction.Iterated.RangeInverse

/-! # Final sparsening roots grouped by their support in the base

Every irreducible subset of the original core has a chosen projected Base-copy.
The homomorphism-embedding into the old Ramsey witness reconstructs an
embedding of the root into Base.  Its finite image is the root's support type.

Roots with the same support T then all become embeddings
Base.induce T -> Orig, exactly the family consumed by Attachment.attach.
-/
namespace StructuralRamsey.RelStructure.FinalSupport

universe u v
variable {L : RelLanguage.{u}}
variable {O VB Y : Type v}
variable (Orig : RelStructure L O)
variable (Base : RelStructure L VB)
variable (Q : RelStructure L Y)
variable (pOrig : O → Y)

/-- Irreducible finite vertex sets of the original core. -/
def Root [Fintype O] :=
  {S : Finset O // (Orig.induce (↑S : Set O)).Irreducible}

namespace Root

variable [Fintype O]
variable (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
variable (hProjected :
  ∀ (S : Set O), (Orig.induce S).Irreducible →
    ∃ β : Embedding Base Q,
      ∀ z : S, ∃ b : VB, pOrig z.1 = β b)

/-- Chosen Base-copy in Q covering the projection of a root. -/
noncomputable def beta (r : Root Orig) : Embedding Base Q :=
  Classical.choose (hProjected (↑r.1 : Set O) r.2)

theorem beta_covers (r : Root Orig) (z : ↥(↑r.1 : Set O)) :
    ∃ b : VB, pOrig z.1 = beta Orig Base Q pOrig hProjected r b :=
  Classical.choose_spec (hProjected (↑r.1 : Set O) r.2) z

/-- Reconstructed induced embedding of the root into its chosen Base-copy. -/
noncomputable def toBase (r : Root Orig) :
    Embedding (Orig.induce (↑r.1 : Set O)) Base :=
  Classical.choose
    (rootEmbeddingIntoBase r.2
      (inclusion Orig (↑r.1 : Set O))
      pOrig hpOrig
      (beta Orig Base Q pOrig hProjected r)
      (beta_covers Orig Base Q pOrig hProjected r))

theorem toBase_compat (r : Root Orig)
    (z : ↥(↑r.1 : Set O)) :
    pOrig z.1 =
      beta Orig Base Q pOrig hProjected r
        (toBase Orig Base Q pOrig hpOrig hProjected r z) :=
  Classical.choose_spec
    (rootEmbeddingIntoBase r.2
      (inclusion Orig (↑r.1 : Set O))
      pOrig hpOrig
      (beta Orig Base Q pOrig hProjected r)
      (beta_covers Orig Base Q pOrig hProjected r)) z

/-- Finite image support of a root inside Base. -/
noncomputable def support (r : Root Orig) : Finset VB :=
  (toBase Orig Base Q pOrig hpOrig hProjected r).imageFinset

/-- Re-read a root as an embedding from its induced support in Base back into
the original core. -/
noncomputable def supportEmbedding (r : Root Orig) :
    Embedding
      (Base.induce
        (↑(support Orig Base Q pOrig hpOrig hProjected r) : Set VB))
      Orig :=
  (inclusion Orig (↑r.1 : Set O)).comp
    (toBase Orig Base Q pOrig hpOrig hProjected r).imageInverse

@[simp] theorem supportEmbedding_toBase (r : Root Orig)
    (x :
      ↥(↑(support Orig Base Q pOrig hpOrig hProjected r) : Set VB)) :
    toBase Orig Base Q pOrig hpOrig hProjected r
        ((toBase Orig Base Q pOrig hpOrig hProjected r).imageInverse x) =
      x.1 := by
  exact
    (toBase Orig Base Q pOrig hpOrig hProjected r).imageInverse_apply x

theorem supportEmbedding_compat (r : Root Orig)
    (x :
      ↥(↑(support Orig Base Q pOrig hpOrig hProjected r) : Set VB)) :
    pOrig (supportEmbedding Orig Base Q pOrig hpOrig hProjected r x) =
      beta Orig Base Q pOrig hProjected r x.1 := by
  change
    pOrig
      ((toBase Orig Base Q pOrig hpOrig hProjected r).imageInverse x).1 =
      beta Orig Base Q pOrig hProjected r x.1
  rw [toBase_compat Orig Base Q pOrig hpOrig hProjected r]
  congr
  exact
    (toBase Orig Base Q pOrig hpOrig hProjected r).imageInverse_apply x

end Root

/-- Roots having exactly one prescribed support inside Base. -/
def AtSupport [Fintype O]
    (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
    (hProjected :
      ∀ (S : Set O), (Orig.induce S).Irreducible →
        ∃ β : Embedding Base Q,
          ∀ z : S, ∃ b : VB, pOrig z.1 = β b)
    (T : Finset VB) :=
  {r : Root Orig //
    Root.support Orig Base Q pOrig hpOrig hProjected r = T}

namespace AtSupport

variable [Fintype O]
variable (hpOrig : Orig.IsHomomorphismEmbedding Q pOrig)
variable (hProjected :
  ∀ (S : Set O), (Orig.induce S).Irreducible →
    ∃ β : Embedding Base Q,
      ∀ z : S, ∃ b : VB, pOrig z.1 = β b)
variable (T : Finset VB)

/-- A root in the T-support class becomes an embedding Base|T -> Orig. -/
noncomputable def embedding
    (r : AtSupport Orig Base Q pOrig hpOrig hProjected T) :
    Embedding (Base.induce (↑T : Set VB)) Orig :=
  (inclusion Orig (↑r.1.1 : Set O)).comp
    (Root.toBase Orig Base Q pOrig hpOrig hProjected r.1).imageInverseAt
      T r.2

theorem embedding_compat
    (r : AtSupport Orig Base Q pOrig hpOrig hProjected T)
    (x : ↥(↑T : Set VB)) :
    pOrig (embedding Orig Base Q pOrig hpOrig hProjected T r x) =
      Root.beta Orig Base Q pOrig hProjected r.1 x.1 := by
  change
    pOrig
      ((Root.toBase Orig Base Q pOrig hpOrig hProjected r.1).
        imageInverseAt T r.2 x).1 =
      Root.beta Orig Base Q pOrig hProjected r.1 x.1
  rw [Root.toBase_compat Orig Base Q pOrig hpOrig hProjected r.1]
  congr
  exact
    (Root.toBase Orig Base Q pOrig hpOrig hProjected r.1).
      imageInverseAt_apply T r.2 x

end AtSupport
end StructuralRamsey.RelStructure.FinalSupport
