import PartiteConstruction.Relational.Attachment
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Folding a fixed-support multi-attachment to a common target

The final sparsening construction groups roots by their image support inside
the base.  One group is exactly `Attachment.attach Base S Core f`: arbitrarily
many copies of `Base`, all glued over the same abstract support `Base.induce S`
but along different embeddings into the core.

Compatible maps of the core and of every copy fold to one map of the whole
attachment.  If the core map is a homomorphism-embedding and each copy map is
an embedding, the folded map is again a homomorphism-embedding.
-/
namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {VB W I Y : Type v}
variable {Base : RelStructure L VB}
variable {S : Set VB}
variable {Core : RelStructure L W}
variable {Q : RelStructure L Y}
variable {f : I → Embedding (Base.induce S) Core}

/-- Fold compatible core/copy maps through a simultaneous attachment. -/
def fold
    (pCore : W → Y)
    (pCopy : I → VB → Y) :
    Vertex S (W := W) (I := I) → Y
  | .inl w => pCore w
  | .inr (i, x) => pCopy i x.1

@[simp] theorem fold_core
    (pCore : W → Y) (pCopy : I → VB → Y) (w : W) :
    fold pCore pCopy (Sum.inl w :
      Vertex S (W := W) (I := I)) = pCore w :=
  rfl

/-- On an attached copy, the fold agrees with that copy's target map whenever
the core and copy maps agree on the support. -/
theorem fold_copy
    (pCore : W → Y)
    (pCopy : I → VB → Y)
    (hcompat : ∀ i : I, ∀ x : ↥S,
      pCore (f i x) = pCopy i x.1)
    (i : I) (b : VB) :
    fold pCore pCopy (copyMap Base S Core f i b) = pCopy i b := by
  classical
  by_cases hb : b ∈ S
  · let x : ↥S := ⟨b, hb⟩
    rw [copyMap_mem i b hb]
    change pCore (f i x) = pCopy i b
    exact hcompat i x
  · rw [copyMap_not_mem i b hb]
    rfl

/-- Compatible target embeddings on all copies and a homomorphism-embedding on
the core give a homomorphism-embedding of the whole simultaneous attachment. -/
theorem fold_isHomomorphismEmbedding
    (pCore : W → Y)
    (pCopy : I → Embedding Base Q)
    (hcompat : ∀ i : I, ∀ x : ↥S,
      pCore (f i x) = pCopy i x.1)
    (hpCore : Core.IsHomomorphismEmbedding Q pCore) :
    (attach Base S Core f).IsHomomorphismEmbedding Q
      (fold pCore (fun i => pCopy i)) := by
  classical
  let F : Vertex S (W := W) (I := I) → Y :=
    fold pCore (fun i => pCopy i)
  constructor
  · intro Rel z hz
    rcases hz with ⟨x, hx, hzx⟩ | ⟨i, x, hx, hzx⟩
    · have hQ : Q.rel Rel (pCore ∘ x) :=
        hpCore.map_rel hx
      convert hQ using 1
      funext k
      have hk := congrFun hzx k
      change F (z k) = pCore (x k)
      rw [hk]
      rfl
    · have hQ : Q.rel Rel ((pCopy i) ∘ x) :=
        ((pCopy i).map_rel_iff Rel x).mpr hx
      convert hQ using 1
      funext k
      have hk := congrFun hzx k
      change F (z k) = pCopy i (x k)
      rw [hk]
      exact fold_copy pCore (fun j => pCopy j) hcompat i (x k)
  · intro T hT
    let Whole := attach Base S Core f
    let inc : Embedding (Whole.induce T) Whole :=
      inclusion Whole T
    rcases irreducible_core_or_copy
        (B := Base) (S := S) (D := Core) (f := f) T hT with
      hcore | ⟨i, hcopy⟩
    · have hrange :
          ∀ z : T, ∃ w : W,
            inc z = coreEmbedding Base S Core f w := by
        intro z
        obtain ⟨w, hw⟩ := hcore z
        exact ⟨w, hw⟩
      let eCore : Embedding (Whole.induce T) Core :=
        inc.factorThroughRange (coreEmbedding Base S Core f) hrange
      obtain ⟨g, hg⟩ :=
        hpCore.after_irreducible_embedding hT eCore
      refine ⟨g, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        g z = pCore (eCore z) := hg z
        _ = F (coreEmbedding Base S Core f (eCore z)) := by
          rfl
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm
    · have hrange :
          ∀ z : T, ∃ b : VB,
            inc z = copyEmbedding Base S Core f i b := by
        intro z
        obtain ⟨b, hb⟩ := hcopy z
        exact ⟨b, hb⟩
      let eBase : Embedding (Whole.induce T) Base :=
        inc.factorThroughRange (copyEmbedding Base S Core f i) hrange
      refine ⟨(pCopy i).comp eBase, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        pCopy i (eBase z) =
            F (copyEmbedding Base S Core f i (eBase z)) := by
          symm
          exact fold_copy pCore (fun j => pCopy j) hcompat i (eBase z)
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm

end StructuralRamsey.RelStructure.Attachment
