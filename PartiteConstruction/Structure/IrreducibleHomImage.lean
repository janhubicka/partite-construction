import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Irreducible homomorphic images

The EHN functional partite power uses coordinate projections which are full
homomorphisms but need not be injective.  We show that the image of an
irreducible structure under a surjective full homomorphism is irreducible.

The proof is the classical free-decomposition pullback: a proper free
decomposition of the image pulls back to a proper free decomposition of the
source.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V : Type v}

/-- Preimages of closed sets under full homomorphisms are closed. -/
theorem IsHomomorphism.preimage_isClosed
    {A : Structure L U} {B : Structure L V}
    {f : U → V} (hf : A.IsHomomorphism B f)
    (S : Set V) (hS : B.IsClosed S) :
    A.IsClosed {a | f a ∈ S} := by
  intro F x hx y hy
  have hfy : f y ∈ B.func F (f ∘ x) := by
    have h :
        f y ∈ Structure.imageSet f (A.func F x) :=
      ⟨y, hy, rfl⟩
    rw [hf.2 F x] at h
    exact h
  exact hS F (f ∘ x) hx hfy

/-- The range of a full homomorphism is function-closed. -/
theorem IsHomomorphism.range_isClosed
    {A : Structure L U} {B : Structure L V}
    {f : U → V} (hf : A.IsHomomorphism B f) :
    B.IsClosed (Set.range f) := by
  intro F x hx y hy
  have hargs : ∀ i, ∃ a : U, f a = x i := fun i => hx i
  choose a ha using hargs
  have hxeq : f ∘ a = x := by
    funext i
    exact ha i
  have hy' : y ∈ B.func F (f ∘ a) := by
    rw [hxeq]
    exact hy
  rw [← hf.2 F a] at hy'
  rcases hy' with ⟨b, hb, hby⟩
  exact ⟨b, hby⟩

/-- Restrict a homomorphism to a closed substructure containing its range. -/
theorem IsHomomorphism.codRestrict
    {A : Structure L U} {B : Structure L V}
    {f : U → V} (hf : A.IsHomomorphism B f)
    (S : Set V) (hS : B.IsClosed S)
    (hrange : ∀ a, f a ∈ S) :
    A.IsHomomorphism (B.induce S hS)
      (fun a => ⟨f a, hrange a⟩) := by
  constructor
  · intro R x hx
    change B.rel R (f ∘ x)
    exact hf.1 R x hx
  · intro F x
    ext y
    constructor
    · rintro ⟨a, ha, hya⟩
      have hfa : f a ∈ B.func F (f ∘ (Subtype.val ∘ x)) := by
        have himg :
            f a ∈ Structure.imageSet f
              (A.func F (Subtype.val ∘ x)) :=
          ⟨a, ha, rfl⟩
        rw [hf.2 F (Subtype.val ∘ x)] at himg
        exact himg
      have hyval : y.1 = f a := congrArg Subtype.val hya
      simpa [hyval] using hfa
    · intro hy
      have hyB :
          y.1 ∈ B.func F (f ∘ (Subtype.val ∘ x)) := hy
      rw [← hf.2 F (Subtype.val ∘ x)] at hyB
      rcases hyB with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hfa.symm

/-- Pull a proper free decomposition back through a surjective homomorphism. -/
theorem ProperFreeDecomposition.pullback_surjective
    {A : Structure L U} {B : Structure L V}
    (d : ProperFreeDecomposition B)
    {f : U → V} (hf : A.IsHomomorphism B f)
    (hsurj : Function.Surjective f) :
    Nonempty (ProperFreeDecomposition A) := by
  classical
  let Lset : Set U := {a | f a ∈ d.left}
  let Rset : Set U := {a | f a ∈ d.right}
  have hLclosed : A.IsClosed Lset :=
    hf.preimage_isClosed d.left d.leftClosed
  have hRclosed : A.IsClosed Rset :=
    hf.preimage_isClosed d.right d.rightClosed
  have hLproper : Lset ≠ Set.univ := by
    intro h
    apply d.leftProper
    ext b
    constructor
    · intro _
      exact Set.mem_univ b
    · intro _
      obtain ⟨a, rfl⟩ := hsurj b
      have ha : a ∈ Lset := by rw [h]; exact Set.mem_univ a
      exact ha
  have hRproper : Rset ≠ Set.univ := by
    intro h
    apply d.rightProper
    ext b
    constructor
    · intro _
      exact Set.mem_univ b
    · intro _
      obtain ⟨a, rfl⟩ := hsurj b
      have ha : a ∈ Rset := by rw [h]; exact Set.mem_univ a
      exact ha
  let Mset : Set U := Lset ∩ Rset
  have hMclosed : A.IsClosed Mset := by
    intro F0 x hx y hy
    exact ⟨hLclosed F0 x (fun i => (hx i).1) hy,
      hRclosed F0 x (fun i => (hx i).2) hy⟩
  let AL := A.induce Lset hLclosed
  let AR := A.induce Rset hRclosed
  let AM := A.induce Mset hMclosed
  let mL : Embedding AM AL := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun q : Lset => q.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F0 x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyr : y.1 ∈ Rset :=
          hRclosed F0 (Subtype.val ∘ x)
            (fun i => (x i).2.2) hy
        exact ⟨⟨y.1, ⟨y.2, hyr⟩⟩, hy, rfl⟩
  }
  let mR : Embedding AM AR := {
    toFun := fun x => ⟨x.1, x.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun q : Rset => q.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F0 x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyl : y.1 ∈ Lset :=
          hLclosed F0 (Subtype.val ∘ x)
            (fun i => (x i).2.1) hy
        exact ⟨⟨y.1, ⟨hyl, y.2⟩⟩, hy, rfl⟩
  }
  let iL : Embedding AL A := inclusion A Lset hLclosed
  let iR : Embedding AR A := inclusion A Rset hRclosed
  rcases d.free with ⟨H, D, sL, sR, hfree⟩
  have hInternal : IsFreeAmalgam mL mR iL iR := by
    constructor
    · intro a
      have hcover := hfree.covers (f a)
      rcases hcover with ⟨x, hx⟩ | ⟨x, hx⟩
      · have ha : a ∈ Lset := by
          change f a ∈ d.left
          exact ⟨x, hx.symm⟩
        exact Or.inl ⟨⟨a, ha⟩, rfl⟩
      · have ha : a ∈ Rset := by
          change f a ∈ d.right
          exact ⟨x, hx.symm⟩
        exact Or.inr ⟨⟨a, ha⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have huv : a.1 = b.1 := hab
        let z : Mset := ⟨a.1, ⟨a.2, by rw [huv]; exact b.2⟩⟩
        exact ⟨z, rfl, by apply Subtype.ext; exact huv.symm⟩
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        have hfz : B.rel R (f ∘ z) := hf.1 R z hz
        rcases (hfree.rel_iff R (f ∘ z)).mp hfz with
          ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · have hmem : ∀ k, z k ∈ Lset := by
            intro k
            change f (z k) ∈ d.left
            exact ⟨x k, (congrFun heq k).symm⟩
          let zl : Fin (L.relArity R) → Lset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inl ⟨zl, hz, rfl⟩
        · have hmem : ∀ k, z k ∈ Rset := by
            intro k
            change f (z k) ∈ d.right
            exact ⟨x k, (congrFun heq k).symm⟩
          let zr : Fin (L.relArity R) → Rset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inr ⟨zr, hz, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
    · intro F0 x y
      constructor
      · intro hy
        have hfy : f y ∈ B.func F0 (f ∘ x) := by
          have himg :
              f y ∈ Structure.imageSet f (A.func F0 x) :=
            ⟨y, hy, rfl⟩
          rw [hf.2 F0 x] at himg
          exact himg
        rcases (hfree.func_iff F0 (f ∘ x) (f y)).mp hfy with
          ⟨a, b, hb, hargs, hout⟩ |
          ⟨a, b, hb, hargs, hout⟩
        · have hxL : ∀ k, x k ∈ Lset := by
            intro k
            change f (x k) ∈ d.left
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyL : y ∈ Lset := by
            change f y ∈ d.left
            exact ⟨b, hout.symm⟩
          let xl : Fin (L.funcArity F0) → Lset :=
            fun k => ⟨x k, hxL k⟩
          exact Or.inl ⟨xl, ⟨y, hyL⟩, hy, rfl, rfl⟩
        · have hxR : ∀ k, x k ∈ Rset := by
            intro k
            change f (x k) ∈ d.right
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyR : y ∈ Rset := by
            change f y ∈ d.right
            exact ⟨b, hout.symm⟩
          let xr : Fin (L.funcArity F0) → Rset :=
            fun k => ⟨x k, hxR k⟩
          exact Or.inr ⟨xr, ⟨y, hyR⟩, hy, rfl, rfl⟩
      · rintro (⟨a, b, hb, hargs, hout⟩ |
          ⟨a, b, hb, hargs, hout⟩)
        · subst x
          subst y
          exact hb
        · subst x
          subst y
          exact hb
  exact ⟨{
    left := Lset
    right := Rset
    leftClosed := hLclosed
    rightClosed := hRclosed
    leftProper := hLproper
    rightProper := hRproper
    free := ⟨Mset, AM, mL, mR, hInternal⟩
  }⟩

/-- A surjective homomorphic image of an irreducible structure is
irreducible. -/
theorem Irreducible.of_surjective_homomorphism
    {A : Structure L U} {B : Structure L V}
    (hA : A.Irreducible)
    {f : U → V} (hf : A.IsHomomorphism B f)
    (hsurj : Function.Surjective f) :
    B.Irreducible := by
  rw [irreducible_iff_noProperFreeDecomposition]
  rintro ⟨d⟩
  exact hA.noProperFreeDecomposition
    (d.pullback_surjective hf hsurj)

/-- The induced structure on the range of a homomorphism from an irreducible
source is irreducible. -/
theorem Irreducible.range_homomorphism
    {A : Structure L U} {B : Structure L V}
    (hA : A.Irreducible)
    {f : U → V} (hf : A.IsHomomorphism B f) :
    let S : Set V := Set.range f
    let hS : B.IsClosed S := by
      intro F x hx y hy
      have hargs : ∀ i, ∃ a : U, f a = x i := fun i => hx i
      choose a ha using hargs
      have hxeq : f ∘ a = x := by funext i; exact ha i
      have hy' : y ∈ B.func F (f ∘ a) := by rw [hxeq]; exact hy
      rw [← hf.2 F a] at hy'
      rcases hy' with ⟨b, hb, hby⟩
      exact ⟨b, hby⟩
    (B.induce S hS).Irreducible := by
  dsimp
  let S : Set V := Set.range f
  have hS : B.IsClosed S := by
    intro F x hx y hy
    have hargs : ∀ i, ∃ a : U, f a = x i := fun i => hx i
    choose a ha using hargs
    have hxeq : f ∘ a = x := by funext i; exact ha i
    have hy' : y ∈ B.func F (f ∘ a) := by rw [hxeq]; exact hy
    rw [← hf.2 F a] at hy'
    rcases hy' with ⟨b, hb, hby⟩
    exact ⟨b, hby⟩
  let g : U → S := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hg : A.IsHomomorphism (B.induce S hS) g :=
    hf.codRestrict S hS (fun a => ⟨a, rfl⟩)
  have hsurj : Function.Surjective g := by
    intro z
    rcases z.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  exact hA.of_surjective_homomorphism hg hsurj

end StructuralRamsey.Structure
