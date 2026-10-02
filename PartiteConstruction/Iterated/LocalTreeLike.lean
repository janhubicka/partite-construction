import PartiteConstruction.Relational.Homomorphism

/-! # Free amalgams, tree amalgams, and local tree-likeness

Relational versions of the notions used in the iterated partite construction.
The definitions are deliberately explicit about embeddings and relation
reflection so later proofs can reuse them without informal identifications.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X Y : Type v}

/-- Isomorphism of relational structures. -/
structure Iso (A : RelStructure L V) (B : RelStructure L W) where
  toEquiv : V ≃ W
  map_rel_iff : ∀ R x, B.rel R (toEquiv ∘ x) ↔ A.rel R x

namespace Iso

def refl (A : RelStructure L V) : Iso A A where
  toEquiv := Equiv.refl V
  map_rel_iff := fun _ _ => Iff.rfl

def toEmbedding {A : RelStructure L V} {B : RelStructure L W}
    (h : Iso A B) : Embedding A B where
  toFun := h.toEquiv
  injective := h.toEquiv.injective
  map_rel_iff := h.map_rel_iff


end Iso

/-- Every induced substructure is irreducible.  Ordered relational
structures with a complete binary order relation satisfy this condition, and
it is exactly what makes arbitrary overlaps inside an `A`-copy visible to a
homomorphism-embedding as induced substructures. -/
def HereditarilyIrreducible (A : RelStructure L U) : Prop :=
  ∀ S : Set U, (A.induce S).Irreducible

theorem HereditarilyIrreducible.irreducible
    {A : RelStructure L U} (hA : HereditarilyIrreducible A) :
    A.Irreducible := by
  intro x y hxy
  let xu : (Set.univ : Set U) := ⟨x, Set.mem_univ x⟩
  let yu : (Set.univ : Set U) := ⟨y, Set.mem_univ y⟩
  have hxu : xu ≠ yu := by
    intro h
    exact hxy (congrArg Subtype.val h)
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ :=
    hA (Set.univ : Set U) hxu
  change A.rel R (Subtype.val ∘ z) at hz
  exact ⟨R, Subtype.val ∘ z, i, j, hz,
    congrArg Subtype.val hzi, congrArg Subtype.val hzj⟩

/-- Any structure embedding into a hereditarily irreducible structure is
irreducible. -/
theorem HereditarilyIrreducible.of_embedding
    {A : RelStructure L U} {D : RelStructure L V}
    (hA : HereditarilyIrreducible A) (e : Embedding D A) :
    D.Irreducible := by
  let S : Set U := Set.range e
  have hS : (A.induce S).Irreducible := hA S
  intro x y hxy
  let xs : S := ⟨e x, ⟨x, rfl⟩⟩
  let ys : S := ⟨e y, ⟨y, rfl⟩⟩
  have hxsys : xs ≠ ys := by
    intro h
    apply hxy
    apply e.injective
    exact congrArg Subtype.val h
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxsys
  let q : Fin (L.arity R) → V :=
    fun k => Classical.choose (z k).property
  have hq (k : Fin (L.arity R)) : e (q k) = (z k).1 :=
    Classical.choose_spec (z k).property
  have hAz : A.rel R (e ∘ q) := by
    change A.rel R (Subtype.val ∘ z) at hz
    convert hz using 1
    funext k
    simpa [Function.comp_apply] using hq k
  have hDz : D.rel R q := (e.map_rel_iff R q).mp hAz
  have hqi : q i = x := by
    apply e.injective
    calc
      e (q i) = (z i).1 := hq i
      _ = xs.1 := congrArg Subtype.val hzi
      _ = e x := rfl
  have hqj : q j = y := by
    apply e.injective
    calc
      e (q j) = (z j).1 := hq j
      _ = ys.1 := congrArg Subtype.val hzj
      _ = e y := rfl
  exact ⟨R, q, i, j, hDz, hqi, hqj⟩

/-- The image of an embedding is contained in some irreducible substructure. -/
def Embedding.ContainedInIrreducible
    {A : RelStructure L U} {B : RelStructure L V}
    (f : Embedding A B) : Prop :=
  ∃ S : Set V, (B.induce S).Irreducible ∧ ∀ x : U, f x ∈ S

/-- An embedded substructure whose image lies inside an embedded copy of an
irreducible structure satisfies the gluing-side condition. -/
theorem Embedding.containedInIrreducible_of_range_subset
    {D : RelStructure L U} {A : RelStructure L V}
    {T : RelStructure L W}
    (hA : A.Irreducible) (α : Embedding A T) (g : Embedding D T)
    (h : ∀ d, ∃ a, g d = α a) :
    g.ContainedInIrreducible := by
  let S : Set W := Set.range α
  refine ⟨S, hA.range_embedding α, ?_⟩
  intro d
  obtain ⟨a, ha⟩ := h d
  exact ⟨a, ha.symm⟩


/-- Under hereditary irreducibility, a homomorphism-embedding is an
ordinary embedding on the image of every embedded substructure of `A`. -/
theorem IsHomomorphismEmbedding.on_substructure_of_hereditarilyIrreducible
    {A : RelStructure L U} {C : RelStructure L V} {T : RelStructure L W}
    (hA : HereditarilyIrreducible A) (S : Set U)
    (e : Embedding (A.induce S) C)
    {f : V → W} (hf : C.IsHomomorphismEmbedding T f) :
    ∃ g : Embedding (A.induce S) T, ∀ x, g x = f (e x) := by
  exact hf.after_irreducible_embedding (hA S) e

/-- Factor an embedding through another embedding whose range contains it. -/
noncomputable def Embedding.factorThroughRange
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    (e : Embedding A C) (i : Embedding B C)
    (h : ∀ x : U, ∃ b : V, e x = i b) :
    Embedding A B where
  toFun x := Classical.choose (h x)
  injective := by
    intro x y hxy
    apply e.injective
    calc
      e x = i (Classical.choose (h x)) := Classical.choose_spec (h x)
      _ = i (Classical.choose (h y)) := congrArg i hxy
      _ = e y := (Classical.choose_spec (h y)).symm
  map_rel_iff := by
    intro R x
    let q : U → V := fun a => Classical.choose (h a)
    have heq : i ∘ (q ∘ x) = e ∘ x := by
      funext k
      exact (Classical.choose_spec (h (x k))).symm
    calc
      B.rel R (q ∘ x) ↔ C.rel R (i ∘ (q ∘ x)) :=
        (i.map_rel_iff R (q ∘ x)).symm
      _ ↔ C.rel R (e ∘ x) := by rw [heq]
      _ ↔ A.rel R x := e.map_rel_iff R x

/-- A concrete relational structure is the free amalgam of `A` and `B`
over `D` when it is covered by induced copies of the two sides, those copies
intersect exactly in the prescribed common image, and every relation tuple
comes wholly from one side. -/
structure IsFreeAmalgam
    {D : RelStructure L U} {A : RelStructure L V}
    {B : RelStructure L W} {C : RelStructure L X}
    (fA : Embedding D A) (fB : Embedding D B)
    (iA : Embedding A C) (iB : Embedding B C) : Prop where
  covers : ∀ z : X, (∃ a : V, z = iA a) ∨ (∃ b : W, z = iB b)
  overlap : ∀ a : V, ∀ b : W,
    iA a = iB b ↔ ∃ d : U, a = fA d ∧ b = fB d
  rel_iff : ∀ R z,
    C.rel R z ↔
      (∃ x : Fin (L.arity R) → V, A.rel R x ∧ z = iA ∘ x) ∨
      (∃ y : Fin (L.arity R) → W, B.rel R y ∧ z = iB ∘ y)

namespace IsFreeAmalgam

/-- Every irreducible substructure of a free amalgam lies on one side. -/
theorem irreducible_side
    {D : RelStructure L U} {A : RelStructure L V}
    {B : RelStructure L W} {C : RelStructure L X}
    {fA : Embedding D A} {fB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hfree : IsFreeAmalgam fA fB iA iB)
    (S : Set X) (hS : (C.induce S).Irreducible) :
    (∀ z : S, ∃ a : V, z.1 = iA a) ∨
      (∀ z : S, ∃ b : W, z.1 = iB b) := by
  classical
  by_cases hleft : ∀ z : S, ∃ a : V, z.1 = iA a
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨z₀, hz₀⟩ := hleft
    obtain hz₀side | hz₀side := hfree.covers z₀.1
    · rcases hz₀side with ⟨a, ha⟩
      exact (hz₀ a ha).elim
    · refine Or.inr ?_
      intro z
      by_cases hzz : z = z₀
      · subst z
        exact hz₀side
      · obtain ⟨R, x, k, l, hx, hxk, hxl⟩ := hS hzz
        change C.rel R (Subtype.val ∘ x) at hx
        rcases (hfree.rel_iff R (Subtype.val ∘ x)).mp hx with hArel | hBrel
        · rcases hArel with ⟨y, hy, heq⟩
          have hz₀left : ∃ a : V, z₀.1 = iA a := by
            refine ⟨y l, ?_⟩
            have h := congrFun heq l
            simpa only [Function.comp_apply, hxl] using h
          rcases hz₀left with ⟨a, ha⟩
          exact (hz₀ a ha).elim
        · rcases hBrel with ⟨y, hy, heq⟩
          refine ⟨y k, ?_⟩
          have h := congrFun heq k
          simpa only [Function.comp_apply, hxk] using h

end IsFreeAmalgam


/-- Tree amalgams of copies of a fixed relational structure, following the
survey definition.  Every gluing takes place over a substructure whose image
on each side lies inside an irreducible substructure. -/
inductive TreeAmalgam (Base : RelStructure L V) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W}
      (h : Iso Base T) : TreeAmalgam Base W T
  | glue
      {W₁ W₂ Z W : Type v}
      {T₁ : RelStructure L W₁} {T₂ : RelStructure L W₂}
      {D : RelStructure L Z} {T : RelStructure L W}
      (h₁ : TreeAmalgam Base W₁ T₁)
      (h₂ : TreeAmalgam Base W₂ T₂)
      (f₁ : Embedding D T₁) (f₂ : Embedding D T₂)
      (hc₁ : f₁.ContainedInIrreducible)
      (hc₂ : f₂.ContainedInIrreducible)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      TreeAmalgam Base W T

namespace TreeAmalgam

/-- Every embedded irreducible structure in a tree amalgam is contained in
one of the constituent copies of the base structure. -/
theorem irreducible_contained_in_copy
    {Base : RelStructure L V} {T : RelStructure L W}
    (hT : TreeAmalgam Base W T)
    {A : RelStructure L U} (hA : A.Irreducible)
    (e : Embedding A T) :
    ∃ j : Embedding Base T, ∀ a : U, ∃ b : V, e a = j b := by
  induction hT with
  | copy h =>
      let j := h.toEmbedding
      refine ⟨j, ?_⟩
      intro a
      refine ⟨h.toEquiv.symm (e a), ?_⟩
      change e a = h.toEquiv (h.toEquiv.symm (e a))
      exact (h.toEquiv.apply_symm_apply (e a)).symm
  | @glue W₁ W₂ Z W T₁ T₂ D T h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      let S : Set W := Set.range e
      have hS : (T.induce S).Irreducible := hA.range_embedding e
      rcases hfree.irreducible_side S hS with hleft | hright
      · have he : ∀ a : U, ∃ x : W₁, e a = i₁ x := by
          intro a
          exact hleft ⟨e a, ⟨a, rfl⟩⟩
        let e₁ : Embedding A T₁ := e.factorThroughRange i₁ he
        obtain ⟨j₁, hj₁⟩ := ih₁ e₁ hA
        refine ⟨i₁.comp j₁, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₁ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        change e a = i₁ (j₁ b)
        calc
          e a = i₁ (e₁ a) := hea
          _ = i₁ (j₁ b) := congrArg i₁ hb
      · have he : ∀ a : U, ∃ x : W₂, e a = i₂ x := by
          intro a
          exact hright ⟨e a, ⟨a, rfl⟩⟩
        let e₂ : Embedding A T₂ := e.factorThroughRange i₂ he
        obtain ⟨j₂, hj₂⟩ := ih₂ e₂ hA
        refine ⟨i₂.comp j₂, ?_⟩
        intro a
        obtain ⟨b, hb⟩ := hj₂ a
        refine ⟨b, ?_⟩
        have hea := Classical.choose_spec (he a)
        change e a = i₂ (j₂ b)
        calc
          e a = i₂ (e₂ a) := hea
          _ = i₂ (j₂ b) := congrArg i₂ hb

end TreeAmalgam


/-- Relational formalization of the survey's `(A,B,n)`-local tree-likeness.
For every induced substructure on at most `n` vertices there is a
homomorphism-embedding into a tree amalgam of copies of `B`, and every
`A`-copy meets that small substructure inside some `A`-copy of the target. -/
def LocallyTreeLike
    (A : RelStructure L U) (B : RelStructure L V)
    (C : RelStructure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T,
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a'


namespace LocallyTreeLike

variable {A : RelStructure L U} {B : RelStructure L V}
  {C : RelStructure L W} {m n : ℕ}

/-- Pull a local-tree witness back along a homomorphism-embedding whenever
the image of the tested finite set is within the available size bound. -/
theorem witness_of_homEmbedding_image
    {D : RelStructure L X}
    (hA : A.Irreducible)
    (hD : LocallyTreeLike A B D m)
    (p : W → X) (hp : C.IsHomomorphismEmbedding D p)
    (S : Finset W) (hcard : (S.image p).card ≤ m) :
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam B Y T ∧
      ∃ f : ↥(↑S : Set W) → Y,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T,
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f ⟨α a, ha⟩ = α' a' := by
  classical
  obtain ⟨Y, T, hTree, g, hg, hctrl⟩ := hD (S.image p) hcard
  let pS : ↥(↑S : Set W) → ↥(↑(S.image p) : Set X) :=
    fun x => ⟨p x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (RelStructure.inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hToD :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding D
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hRange :
      ∀ x : ↥(↑S : Set W), (p ∘ Subtype.val) x ∈ (↑(S.image p) : Set X) := by
    intro x
    exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
  have hpS :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding
        (D.induce (↑(S.image p) : Set X)) pS := by
    exact hToD.codRestrict (↑(S.image p) : Set X) hRange
  let f : ↥(↑S : Set W) → Y := g ∘ pS
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f :=
    hg.comp hpS
  refine ⟨Y, T, hTree, f, hf, ?_⟩
  intro α
  obtain ⟨αD, hαD⟩ := hp.after_irreducible_embedding hA α
  obtain ⟨α', hα'⟩ := hctrl αD
  refine ⟨α', ?_⟩
  intro a ha
  have himg : αD a ∈ S.image p := by
    apply Finset.mem_image.mpr
    refine ⟨α a, ha, ?_⟩
    exact (hαD a).symm
  obtain ⟨a', ha'⟩ := hα' a himg
  refine ⟨a', ?_⟩
  change g (pS ⟨α a, ha⟩) = α' a'
  have hsub :
      pS ⟨α a, ha⟩ =
        (⟨αD a, himg⟩ : ↥(↑(S.image p) : Set X)) := by
    apply Subtype.ext
    exact (hαD a).symm
  rw [hsub]
  exact ha'

/-- Local tree-likeness is monotone in the size bound. -/
theorem mono (h : LocallyTreeLike A B C n) (hmn : m ≤ n) :
    LocallyTreeLike A B C m := by
  intro S hS
  exact h S (hS.trans hmn)

/-- If `A ↪ B ↪ C`, then `C` is `(A,B,0)`-locally
tree-like.  The copy `B ↪ C` also synchronizes nullary relations on the
empty induced substructure. -/
theorem zero_of_embeddings
    (eAB : Embedding A B) (jBC : Embedding B C) :
    LocallyTreeLike A B C 0 := by
  intro S hS
  have hEmpty : S = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  subst S
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B), ?_⟩
  let f : ↥(↑(∅ : Finset W) : Set W) → V :=
    fun x => (Finset.notMem_empty x.1 x.2).elim
  have hf :
      (C.induce (↑(∅ : Finset W) : Set W)).IsHomomorphismEmbedding B f := by
    apply IsHomomorphismEmbedding.of_map_reflect
    · intro R x hx
      have htarget : C.rel R (jBC ∘ (f ∘ x)) := by
        change C.rel R (Subtype.val ∘ x) at hx
        convert hx using 1
        funext i
        exact (Finset.notMem_empty (x i).1 (x i).2).elim
      exact (jBC.map_rel_iff R (f ∘ x)).mp htarget
    · intro T hT x hx y hy hxy
      exact (Finset.notMem_empty x.1.1 x.1.2).elim
    · intro T hT R x hxT hB
      change C.rel R (Subtype.val ∘ x)
      have htarget : C.rel R (jBC ∘ (f ∘ (Subtype.val ∘ x))) :=
        (jBC.map_rel_iff R (f ∘ (Subtype.val ∘ x))).mpr hB
      convert htarget using 1
      funext i
      exact (Finset.notMem_empty (x i).1.1 (x i).1.2).elim
  refine ⟨f, hf, ?_⟩
  intro α
  refine ⟨eAB, ?_⟩
  intro a ha
  exact (Finset.notMem_empty _ ha).elim

/-- If `C` homomorphism-embeds into irreducible `A`, and `A` embeds into
`B`, then `C` is locally tree-like at every scale, witnessed by the
one-copy tree amalgam `B`. -/
theorem of_homEmbedding_to_base
    (hA : A.Irreducible) (eAB : Embedding A B)
    (p : W → U) (hp : C.IsHomomorphismEmbedding A p) (n : ℕ) :
    LocallyTreeLike A B C n := by
  intro S _
  refine ⟨V, B, TreeAmalgam.copy (Iso.refl B), ?_⟩
  let f : ↥(↑S : Set W) → V := fun x => eAB (p x.1)
  have hIncl :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding C Subtype.val :=
    (RelStructure.inclusion C (↑S : Set W)).isHomomorphismEmbedding
  have hRestrict :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding A
        (p ∘ Subtype.val) :=
    hp.comp hIncl
  have hf :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding B f := by
    change (C.induce (↑S : Set W)).IsHomomorphismEmbedding B
      (eAB ∘ (p ∘ Subtype.val))
    exact eAB.isHomomorphismEmbedding.comp hRestrict
  refine ⟨f, hf, ?_⟩
  intro α
  obtain ⟨g, hg⟩ := hp.after_irreducible_embedding hA α
  let α' : Embedding A B := eAB.comp g
  refine ⟨α', ?_⟩
  intro a ha
  refine ⟨a, ?_⟩
  change eAB (p (α a)) = eAB (g a)
  exact congrArg eAB (hg a).symm

end LocallyTreeLike

end StructuralRamsey.RelStructure
