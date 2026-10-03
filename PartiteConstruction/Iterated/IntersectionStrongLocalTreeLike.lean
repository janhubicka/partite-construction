import PartiteConstruction.Iterated.LocalTreeLike

/-! # Intersection-strong local tree witnesses

The ordinary local-tree invariant only says that the image of the tested
part of every ambient A-copy is contained in some target A-copy.  For a
reducible intersection this does not ensure that the witness map is induced
there, and independently chosen side witnesses can have incompatible kernels.

The strengthened internal invariant below additionally records an embedding
on every tested intersection with an ambient A-copy.  It still implies the
survey's ordinary local-tree property.  The point is to carry enough
restriction data through the iterated construction without requiring every
substructure of A itself to be irreducible.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- Local tree-likeness together with an induced restriction on the tested
intersection of every ambient A-copy. -/
def IntersectionStrongLocallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T,
            (∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a') ∧
            ∃ g : Embedding
                (A.induce {a : U | α a ∈ S}) T,
              ∀ x, g x = f ⟨α x.1, x.2⟩

namespace IntersectionStrongLocallyTreeLike

variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {D : RelStructure L X}
variable {m n : ℕ}

/-- Forget the intersection-embedding data. -/
theorem toLocallyTreeLike
    (h : IntersectionStrongLocallyTreeLike A B C n) :
    LocallyTreeLike A B C n := by
  intro S hS
  obtain ⟨Y, T, hTree, f, hf, hctrl⟩ := h S hS
  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro α
  obtain ⟨α', hα', _⟩ := hctrl α
  exact ⟨α', hα'⟩

/-- Monotonicity in the tested size. -/
theorem mono
    (h : IntersectionStrongLocallyTreeLike A B C n) (hmn : m ≤ n) :
    IntersectionStrongLocallyTreeLike A B C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- Level zero is intersection-strong whenever A embeds into B and B into C.
The intersection condition is vacuous because the tested set is empty. -/
theorem zero_of_embeddings
    (eAB : Embedding A B) (jBC : Embedding B C) :
    IntersectionStrongLocallyTreeLike A B C 0 := by
  intro S hS
  have hEmpty : S = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  subst S
  obtain ⟨Y, T, hTree, f, hf, hctrl⟩ :=
    LocallyTreeLike.zero_of_embeddings eAB jBC ∅ (by simp)
  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro α
  obtain ⟨α', hα'⟩ := hctrl α
  refine ⟨α', hα', ?_⟩
  let Hit : Set U := {a : U | α a ∈ (∅ : Finset W)}
  let g : Embedding (A.induce Hit) T :=
    α'.comp (inclusion A Hit)
  refine ⟨g, ?_⟩
  intro x
  exact (Finset.notMem_empty (α x.1) x.2).elim

/-- If C homomorphism-embeds into irreducible A and A embeds into B, the
one-copy B witness is intersection-strong at every level. -/
theorem of_homEmbedding_to_base
    (hA : A.Irreducible) (eAB : Embedding A B)
    (p : W → U) (hp : C.IsHomomorphismEmbedding A p) (n : ℕ) :
    IntersectionStrongLocallyTreeLike A B C n := by
  intro S _
  let f : ↥(↑S : Set W) → V := fun x => eAB (p x.1)
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hRestrict :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding A
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding B f := by
    change (C.induce (↑S : Set W)).IsHomomorphismEmbedding B
      (eAB ∘ (p ∘ Subtype.val))
    exact eAB.isHomomorphismEmbedding.comp hRestrict
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B), f, hf, ?_⟩
  intro α
  obtain ⟨q, hq⟩ := hp.after_irreducible_embedding hA α
  let α' : Embedding A B := eAB.comp q
  refine ⟨α', ?_, ?_⟩
  · intro a ha
    refine ⟨a, ?_⟩
    change eAB (p (α a)) = eAB (q a)
    exact congrArg eAB (hq a).symm
  · let Hit : Set U := {a : U | α a ∈ S}
    let g : Embedding (A.induce Hit) B :=
      α'.comp (inclusion A Hit)
    refine ⟨g, ?_⟩
    intro x
    change eAB (q x.1) = eAB (p (α x.1))
    exact congrArg eAB (hq x.1)

/-- Pull the strengthened invariant back along an induced embedding. -/
theorem pullback_embedding
    (hC : IntersectionStrongLocallyTreeLike A B C n)
    (e : Embedding D C) :
    IntersectionStrongLocallyTreeLike A B D n := by
  classical
  intro S hS
  let I : Finset W := S.image e
  have hcard : I.card = S.card := by
    exact Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  obtain ⟨Y, T, hTree, fC, hfC, hctrlC⟩ := hC I (by
    rw [hcard]
    exact hS)
  let eS : ↥(↑S : Set X) → ↥(↑I : Set W) :=
    fun x => ⟨e x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  let ee : Embedding (D.induce (↑S : Set X)) (C.induce (↑I : Set W)) := {
    toFun := eS
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change C.rel R (e ∘ (Subtype.val ∘ x)) ↔
        D.rel R (Subtype.val ∘ x)
      exact e.map_rel_iff R (Subtype.val ∘ x)
  }
  let f : ↥(↑S : Set X) → Y := fC ∘ ee
  have hf :
      (D.induce (↑S : Set X)).IsHomomorphismEmbedding T f :=
    hfC.comp ee.isHomomorphismEmbedding
  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro α
  obtain ⟨α', hα', gC, hgC⟩ := hctrlC (e.comp α)
  refine ⟨α', ?_, ?_⟩
  · intro a ha
    have hi : e (α a) ∈ I :=
      Finset.mem_image.mpr ⟨α a, ha, rfl⟩
    obtain ⟨a', ha'⟩ := hα' a hi
    refine ⟨a', ?_⟩
    change fC (ee ⟨α a, ha⟩) = α' a'
    have heq :
        ee ⟨α a, ha⟩ =
          (⟨e (α a), hi⟩ : ↥(↑I : Set W)) := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact ha'
  · let HitD : Set U := {a : U | α a ∈ S}
    let HitC : Set U := {a : U | e (α a) ∈ I}
    let incHit : Embedding (A.induce HitD) (A.induce HitC) := {
      toFun := fun x => ⟨x.1, Finset.mem_image.mpr ⟨α x.1, x.2, rfl⟩⟩
      injective := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun q : HitC => q.1) hxy
      map_rel_iff := fun _ _ => Iff.rfl
    }
    let g : Embedding (A.induce HitD) T := gC.comp incHit
    refine ⟨g, ?_⟩
    intro x
    change gC (incHit x) = fC (ee ⟨α x.1, x.2⟩)
    rw [hgC (incHit x)]
    apply congrArg fC
    apply Subtype.ext
    rfl

/-- Pull a strengthened local witness back along a homomorphism-embedding
when the image of the tested set fits the available bound. -/
theorem witness_of_homEmbedding_image
    [DecidableEq X]
    (hA : A.Irreducible)
    (hD : IntersectionStrongLocallyTreeLike A B D m)
    (p : W → X) (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hcard : (S.image p).card ≤ m) :
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T,
            (∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a') ∧
            ∃ g : Embedding (A.induce {a : U | α a ∈ S}) T,
              ∀ x, g x = f ⟨α x.1, x.2⟩ := by
  classical
  let I : Finset X := S.image p
  obtain ⟨Y, T, hTree, gD, hgD, hctrlD⟩ := hD I hcard
  let pS : ↥(↑S : Set W) → ↥(↑I : Set X) :=
    fun x => ⟨p x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hToD :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding D
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hRange : ∀ x : ↥(↑S : Set W), (p ∘ Subtype.val) x ∈ (↑I : Set X) :=
    fun x => Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
  have hpS :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding
        (D.induce (↑I : Set X)) pS :=
    hToD.codRestrict (↑I : Set X) hRange
  let f : ↥(↑S : Set W) → Y := gD ∘ pS
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f :=
    hgD.comp hpS
  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro α
  obtain ⟨αD, hαD⟩ := hp.after_irreducible_embedding hA α
  obtain ⟨αT, hαT, gHitD, hgHitD⟩ := hctrlD αD
  refine ⟨αT, ?_, ?_⟩
  · intro a ha
    have himg : αD a ∈ I := by
      apply Finset.mem_image.mpr
      refine ⟨α a, ha, ?_⟩
      exact (hαD a).symm
    obtain ⟨a', ha'⟩ := hαT a himg
    refine ⟨a', ?_⟩
    change gD (pS ⟨α a, ha⟩) = αT a'
    have hsub :
        pS ⟨α a, ha⟩ =
          (⟨αD a, himg⟩ : ↥(↑I : Set X)) := by
      apply Subtype.ext
      exact (hαD a).symm
    rw [hsub]
    exact ha'
  · let HitC : Set U := {a : U | α a ∈ S}
    let HitD : Set U := {a : U | αD a ∈ I}
    let incHit : Embedding (A.induce HitC) (A.induce HitD) := {
      toFun := fun x => ⟨x.1, by
        apply Finset.mem_image.mpr
        refine ⟨α x.1, x.2, ?_⟩
        exact (hαD x.1).symm⟩
      injective := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun q : HitD => q.1) hxy
      map_rel_iff := fun _ _ => Iff.rfl
    }
    let gHit : Embedding (A.induce HitC) T := gHitD.comp incHit
    refine ⟨gHit, ?_⟩
    intro x
    change gHitD (incHit x) = gD (pS ⟨α x.1, x.2⟩)
    rw [hgHitD (incHit x)]
    apply congrArg gD
    apply Subtype.ext
    exact hαD x.1

end IntersectionStrongLocallyTreeLike
end StructuralRamsey.RelStructure
