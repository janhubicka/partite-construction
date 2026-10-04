import PartiteConstruction.Structure.FreeAmalgamationClass

/-! # Irreducible homomorphic images

A surjective full homomorphic image of an irreducible relation/function
structure is irreducible.  The proof pulls a hypothetical proper free
decomposition of the image back along the homomorphism.
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
    have h : f y ∈ Structure.imageSet f (A.func F x) :=
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
  choose a ha using hx
  have hxeq : f ∘ a = x := by
    funext i
    exact ha i
  have hy' : y ∈ B.func F (f ∘ a) := by
    rw [hxeq]
    exact hy
  rw [← hf.2 F a] at hy'
  rcases hy' with ⟨b, hb, hby⟩
  exact ⟨b, hby⟩

/-- Restrict the codomain of a full homomorphism to a closed substructure
containing its range. -/
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
    · rintro ⟨a, ha, rfl⟩
      change f a ∈ B.func F (f ∘ x)
      have himg : f a ∈ imageSet f (A.func F x) := ⟨a, ha, rfl⟩
      rw [hf.2 F x] at himg
      exact himg
    · intro hy
      change y.1 ∈ B.func F (f ∘ x) at hy
      rw [← hf.2 F x] at hy
      rcases hy with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hfa

/-- Pull a proper free decomposition back through a surjective full
homomorphism. -/
theorem ProperFreeDecomposition.pullback_surjective
    {A : Structure L U} {B : Structure L V}
    (d : ProperFreeDecomposition B)
    {f : U → V} (hf : A.IsHomomorphism B f)
    (hsurj : Function.Surjective f) :
    Nonempty (ProperFreeDecomposition A) := by
  classical
  let Lrange : Set V := Set.range d.leftIn
  let Rrange : Set V := Set.range d.rightIn
  have hLrange : B.IsClosed Lrange := d.leftIn.range_isClosed
  have hRrange : B.IsClosed Rrange := d.rightIn.range_isClosed
  let Lset : Set U := {a | f a ∈ Lrange}
  let Rset : Set U := {a | f a ∈ Rrange}
  have hLclosed : A.IsClosed Lset :=
    hf.preimage_isClosed Lrange hLrange
  have hRclosed : A.IsClosed Rset :=
    hf.preimage_isClosed Rrange hRrange
  have hLproper : ¬ Function.Surjective (inclusion A Lset hLclosed) := by
    intro hinc
    apply d.leftProper
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    obtain ⟨x, hx⟩ := hinc a
    have hmem : f a ∈ Lrange := by
      change f a ∈ Set.range d.leftIn
      rw [← hx]
      exact x.2
    rcases hmem with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    exact hl.trans ha
  have hRproper : ¬ Function.Surjective (inclusion A Rset hRclosed) := by
    intro hinc
    apply d.rightProper
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    obtain ⟨x, hx⟩ := hinc a
    have hmem : f a ∈ Rrange := by
      change f a ∈ Set.range d.rightIn
      rw [← hx]
      exact x.2
    rcases hmem with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    exact hr.trans ha
  let Mset : Set U := Lset ∩ Rset
  have hMclosed : A.IsClosed Mset := by
    intro F0 x hx y hy
    exact ⟨
      hLclosed F0 x (fun i => (hx i).1) hy,
      hRclosed F0 x (fun i => (hx i).2) hy⟩
  let AL := A.induce Lset hLclosed
  let AR := A.induce Rset hRclosed
  let AM := A.induce Mset hMclosed
  let mL : Embedding AM AL := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Lset => z.1) h
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
      exact congrArg (fun z : Rset => z.1) h
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
  have hInternal : IsFreeAmalgam mL mR iL iR := by
    constructor
    · intro a
      rcases d.free.covers (f a) with ⟨l, hl⟩ | ⟨r, hr⟩
      · have ha : a ∈ Lset := ⟨l, hl.symm⟩
        exact Or.inl ⟨⟨a, ha⟩, rfl⟩
      · have ha : a ∈ Rset := ⟨r, hr.symm⟩
        exact Or.inr ⟨⟨a, ha⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have huv : a.1 = b.1 := hab
        let z : Mset := ⟨a.1, ⟨a.2, by simpa [huv] using b.2⟩⟩
        refine ⟨z, rfl, ?_⟩
        apply Subtype.ext
        exact huv.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        have hfz : B.rel R (f ∘ z) := hf.1 R z hz
        rcases (d.free.rel_iff R (f ∘ z)).mp hfz with
          ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · have hmem : ∀ k, z k ∈ Lset := by
            intro k
            exact ⟨x k, (congrFun heq k).symm⟩
          let zl : Fin (L.relArity R) → Lset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inl ⟨zl, hz, rfl⟩
        · have hmem : ∀ k, z k ∈ Rset := by
            intro k
            exact ⟨x k, (congrFun heq k).symm⟩
          let zr : Fin (L.relArity R) → Rset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inr ⟨zr, hz, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
    · intro F0 x y
      constructor
      · intro hy
        have hfy : f y ∈ B.func F0 (f ∘ x) := by
          have himg : f y ∈ imageSet f (A.func F0 x) :=
            ⟨y, hy, rfl⟩
          rw [hf.2 F0 x] at himg
          exact himg
        rcases (d.free.func_iff F0 (f ∘ x) (f y)).mp hfy with
          ⟨a, b, hb, hargs, hout⟩ |
          ⟨a, b, hb, hargs, hout⟩
        · have hxL : ∀ k, x k ∈ Lset := by
            intro k
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyL : y ∈ Lset := ⟨b, hout.symm⟩
          let xl : Fin (L.funcArity F0) → Lset :=
            fun k => ⟨x k, hxL k⟩
          exact Or.inl ⟨xl, ⟨y, hyL⟩, hy, rfl, rfl⟩
        · have hxR : ∀ k, x k ∈ Rset := by
            intro k
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyR : y ∈ Rset := ⟨b, hout.symm⟩
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
    Common := Mset
    Left := Lset
    Right := Rset
    common := AM
    left := AL
    right := AR
    toLeft := mL
    toRight := mR
    leftIn := iL
    rightIn := iR
    free := hInternal
    leftProper := hLproper
    rightProper := hRproper
  }⟩

/-- A surjective full homomorphic image of an irreducible structure is
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
    (B.induce (Set.range f) hf.range_isClosed).Irreducible := by
  let S : Set V := Set.range f
  let hS : B.IsClosed S := hf.range_isClosed
  let g : U → S := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hg : A.IsHomomorphism (B.induce S hS) g :=
    hf.codRestrict S hS (fun a => ⟨a, rfl⟩)
  have hsurj : Function.Surjective g := by
    intro z
    rcases z.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  have hIrr : (B.induce S hS).Irreducible :=
    Irreducible.of_surjective_homomorphism
      (A := A) (B := B.induce S hS) hA hg hsurj
  simpa [S, hS] using hIrr

end StructuralRamsey.Structure
