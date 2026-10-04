import PartiteConstruction.Structure.WeakHomomorphism

/-! # Irreducible weak images and their closed hulls

EHN projections preserve function incidences, not whole fibres. Pulling back
a free decomposition requires only this weak preservation. Surjectivity can
be weakened further: it suffices that the image generates the target under
the functions. In particular the closed hull of the image of an irreducible
structure under a weak homomorphism is irreducible.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- The image of a map generates the target under all function values. -/
def Generates (B : Structure L V) (f : U → V) : Prop :=
  ∀ S : Set V, B.IsClosed S → (∀ a, f a ∈ S) → ∀ b, b ∈ S

theorem generates_of_surjective
    (B : Structure L V) {f : U → V} (hf : Function.Surjective f) :
    B.Generates f := by
  intro S _ hS b
  obtain ⟨a, rfl⟩ := hf b
  exact hS a

/-- Weak homomorphisms, just like full ones, pull closed sets back to closed
sets. Their ranges need not be closed. -/
theorem IsWeakHomomorphism.preimage_isClosed
    {A : Structure L U} {B : Structure L V}
    {f : U → V} (hf : A.IsWeakHomomorphism B f)
    (S : Set V) (hS : B.IsClosed S) :
    A.IsClosed {a | f a ∈ S} := by
  intro F x hx y hy
  exact hS F (f ∘ x) hx (hf.2 F x y hy)

/-- A proper free decomposition pulls back through a generating weak map.
No target function value is lifted through that map in this proof. -/
theorem ProperFreeDecomposition.pullback_generated_weak
    {A : Structure L U} {B : Structure L V}
    (d : ProperFreeDecomposition B)
    {f : U → V} (hf : A.IsWeakHomomorphism B f)
    (hgen : B.Generates f) :
    Nonempty (ProperFreeDecomposition A) := by
  classical
  let Lrange : Set V := Set.range d.leftIn
  let Rrange : Set V := Set.range d.rightIn
  have hLrange : B.IsClosed Lrange := d.leftIn.range_isClosed
  have hRrange : B.IsClosed Rrange := d.rightIn.range_isClosed
  let Lset : Set U := {a | f a ∈ Lrange}
  let Rset : Set U := {a | f a ∈ Rrange}
  have hLclosed : A.IsClosed Lset := hf.preimage_isClosed Lrange hLrange
  have hRclosed : A.IsClosed Rset := hf.preimage_isClosed Rrange hRrange
  have hLproper : ¬ Function.Surjective (inclusion A Lset hLclosed) := by
    intro hinc
    apply d.leftProper
    have himage : ∀ a, f a ∈ Lrange := by
      intro a
      obtain ⟨x, hx⟩ := hinc a
      rw [← hx]
      exact x.2
    exact hgen Lrange hLrange himage
  have hRproper : ¬ Function.Surjective (inclusion A Rset hRclosed) := by
    intro hinc
    apply d.rightProper
    have himage : ∀ a, f a ∈ Rrange := by
      intro a
      obtain ⟨x, hx⟩ := hinc a
      rw [← hx]
      exact x.2
    exact hgen Rrange hRrange himage
  let Mset : Set U := Lset ∩ Rset
  have hMclosed : A.IsClosed Mset := by
    intro F x hx y hy
    exact ⟨hLclosed F x (fun i => (hx i).1) hy,
      hRclosed F x (fun i => (hx i).2) hy⟩
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
      intro F x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyr : y.1 ∈ Rset :=
          hRclosed F (Subtype.val ∘ x) (fun i => (x i).2.2) hy
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
      intro F x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyl : y.1 ∈ Lset :=
          hLclosed F (Subtype.val ∘ x) (fun i => (x i).2.1) hy
        exact ⟨⟨y.1, ⟨hyl, y.2⟩⟩, hy, rfl⟩
  }
  let iL : Embedding AL A := inclusion A Lset hLclosed
  let iR : Embedding AR A := inclusion A Rset hRclosed
  have hInternal : IsFreeAmalgam mL mR iL iR := by
    constructor
    · intro a
      rcases d.free.covers (f a) with ⟨l, hl⟩ | ⟨r, hr⟩
      · exact Or.inl ⟨⟨a, ⟨l, hl.symm⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨a, ⟨r, hr.symm⟩⟩, rfl⟩
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
        rcases (d.free.rel_iff R (f ∘ z)).mp (hf.1 R z hz) with
          ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · have hmem : ∀ k, z k ∈ Lset :=
            fun k => ⟨x k, (congrFun heq k).symm⟩
          exact Or.inl ⟨fun k => ⟨z k, hmem k⟩, hz, rfl⟩
        · have hmem : ∀ k, z k ∈ Rset :=
            fun k => ⟨x k, (congrFun heq k).symm⟩
          exact Or.inr ⟨fun k => ⟨z k, hmem k⟩, hz, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
    · intro F x y
      constructor
      · intro hy
        rcases (d.free.func_iff F (f ∘ x) (f y)).mp (hf.2 F x y hy) with
          ⟨a, b, hb, hargs, hout⟩ | ⟨a, b, hb, hargs, hout⟩
        · have hxL : ∀ k, x k ∈ Lset :=
            fun k => ⟨a k, (congrFun hargs k).symm⟩
          have hyL : y ∈ Lset := ⟨b, hout.symm⟩
          exact Or.inl ⟨fun k => ⟨x k, hxL k⟩, ⟨y, hyL⟩, hy, rfl, rfl⟩
        · have hxR : ∀ k, x k ∈ Rset :=
            fun k => ⟨a k, (congrFun hargs k).symm⟩
          have hyR : y ∈ Rset := ⟨b, hout.symm⟩
          exact Or.inr ⟨fun k => ⟨x k, hxR k⟩, ⟨y, hyR⟩, hy, rfl, rfl⟩
      · rintro (⟨a, b, hb, hargs, hout⟩ | ⟨a, b, hb, hargs, hout⟩)
        · subst x; subst y; exact hb
        · subst x; subst y; exact hb
  exact ⟨{
    Common := Mset, Left := Lset, Right := Rset,
    common := AM, left := AL, right := AR,
    toLeft := mL, toRight := mR, leftIn := iL, rightIn := iR,
    free := hInternal, leftProper := hLproper, rightProper := hRproper
  }⟩

theorem Irreducible.of_generated_weakHomomorphism
    {A : Structure L U} {B : Structure L V} (hA : A.Irreducible)
    {f : U → V} (hf : A.IsWeakHomomorphism B f) (hgen : B.Generates f) :
    B.Irreducible := by
  rw [irreducible_iff_noProperFreeDecomposition]
  rintro ⟨d⟩
  exact hA.noProperFreeDecomposition (d.pullback_generated_weak hf hgen)

theorem Irreducible.of_surjective_weakHomomorphism
    {A : Structure L U} {B : Structure L V} (hA : A.Irreducible)
    {f : U → V} (hf : A.IsWeakHomomorphism B f)
    (hsurj : Function.Surjective f) : B.Irreducible :=
  hA.of_generated_weakHomomorphism hf (generates_of_surjective B hsurj)

/-- The incidence-generated quotient is irreducible even though its quotient
map need not be full. -/
theorem Irreducible.weakImage
    {A : Structure L U} {B : Structure L V} (hA : A.Irreducible)
    {f : U → V} : (weakImage A B f).Irreducible :=
  hA.of_surjective_weakHomomorphism
    (StructuralRamsey.Structure.weakImage.quotientMap_weak
      (A := A) (B := B) (f := f))
    (StructuralRamsey.Structure.weakImage.quotientMap_surjective (f := f))

/-- Least set closed under the functions and containing S. -/
def functionClosure (B : Structure L V) (S : Set V) : Set V :=
  {x | ∀ T : Set V, B.IsClosed T → S ⊆ T → x ∈ T}

theorem subset_functionClosure (B : Structure L V) (S : Set V) :
    S ⊆ B.functionClosure S := fun _ hx _ _ hST => hST hx

theorem functionClosure_isClosed (B : Structure L V) (S : Set V) :
    B.IsClosed (B.functionClosure S) := by
  intro F x hx y hy T hT hST
  exact hT F x (fun i => hx i T hT hST) hy

/-- Restrict a weak map to the closed hull of its range. -/
def closureLift (B : Structure L V) (f : U → V) :
    U → B.functionClosure (Set.range f) :=
  fun a => ⟨f a, subset_functionClosure B (Set.range f) ⟨a, rfl⟩⟩

theorem IsWeakHomomorphism.closureLift
    {A : Structure L U} {B : Structure L V}
    {f : U → V} (hf : A.IsWeakHomomorphism B f) :
    A.IsWeakHomomorphism
      (B.induce (B.functionClosure (Set.range f))
        (B.functionClosure_isClosed (Set.range f))) (closureLift B f) := by
  constructor
  · intro R x hx
    exact hf.1 R x hx
  · intro F x y hy
    exact hf.2 F x y hy

theorem closureLift_generates (B : Structure L V) (f : U → V) :
    (B.induce (B.functionClosure (Set.range f))
      (B.functionClosure_isClosed (Set.range f))).Generates (closureLift B f) := by
  classical
  let H := B.functionClosure (Set.range f)
  have hH : B.IsClosed H := B.functionClosure_isClosed (Set.range f)
  intro T hT hf z
  let S : Set V := {b | ∃ hb : b ∈ H, (⟨b, hb⟩ : H) ∈ T}
  have hS : B.IsClosed S := by
    intro F x hx y hy
    let xs : Fin (L.funcArity F) → H :=
      fun i => ⟨x i, (hx i).choose⟩
    have hxs : ∀ i, xs i ∈ T := fun i => (hx i).choose_spec
    have hyH : y ∈ H := hH F x (fun i => (hx i).choose) hy
    have hyT : (⟨y, hyH⟩ : H) ∈ T := hT F xs hxs hy
    exact ⟨hyH, hyT⟩
  have hfS : Set.range f ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(closureLift B f a).2, hf a⟩
  obtain ⟨hz, hzT⟩ := z.2 S hS hfS
  exact hzT

/-- The closed hull, not the potentially non-closed raw coordinate range,
is the object to which a partite irreducibility invariant can be applied. -/
theorem Irreducible.functionClosure_weakImage
    {A : Structure L U} {B : Structure L V} (hA : A.Irreducible)
    {f : U → V} (hf : A.IsWeakHomomorphism B f) :
    (B.induce (B.functionClosure (Set.range f))
      (B.functionClosure_isClosed (Set.range f))).Irreducible :=
  hA.of_generated_weakHomomorphism hf.closureLift (closureLift_generates B f)

end StructuralRamsey.Structure
