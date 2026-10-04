import PartiteConstruction.Structure.RootedClass

set_option autoImplicit false

/-! # Encoding embeddings which agree on the fixed root -/
namespace StructuralRamsey.Rooted

open StructuralRamsey Structure

universe u v
variable {L : Language.{u}} {R U V : Type v} {n : ℕ}

/-- A full embedding which agrees with the chosen root maps moving vertices to
moving vertices. -/
noncomputable def outsideMap
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r) :
    Outside ρA → Outside ρB :=
  fun x => ⟨e x.1, by
    rintro ⟨r, hr⟩
    apply x.2
    refine ⟨r, ?_⟩
    apply e.injective
    exact (hroot r).trans hr⟩

@[simp] theorem outsideMap_apply
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (x : Outside ρA) :
    (outsideMap e hroot x).1 = e x.1 := rfl

theorem outsideMap_injective
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r) :
    Function.Injective (outsideMap e hroot) := by
  intro x y h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

/-- Filling a rooted pattern commutes with a root-compatible embedding. -/
theorem fill_map
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (p : Pattern n R) (x : Fin n → Outside ρA) :
    e ∘ Pattern.fill ρA p x =
      Pattern.fill ρB p (outsideMap e hroot ∘ x) := by
  funext i
  cases h : p.fixed i with
  | some r =>
      simpa [Pattern.fill, h] using hroot r
  | none =>
      simp [Pattern.fill, h, outsideMap, Function.comp_apply]

/-- Membership of a fixed root value in a function fibre is reflected by a
root-compatible full embedding. -/
theorem root_func_iff
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → U) (r : R) :
    ρB r ∈ B.func F (e ∘ x) ↔ ρA r ∈ A.func F x := by
  have hm := e.map_func F x
  constructor
  · intro hr
    rw [← hm] at hr
    rcases hr with ⟨z, hz, hez⟩
    have hzroot : z = ρA r := by
      apply e.injective
      exact hez.trans (hroot r).symm
    simpa [hzroot] using hz
  · intro hr
    have himg : e (ρA r) ∈ Structure.imageSet e (A.func F x) :=
      ⟨ρA r, hr, rfl⟩
    rw [hm] at himg
    rwa [hroot r] at himg

/-- Full function-fibre preservation restricts to outside outputs for
arbitrary (possibly mixed root/moving) argument tuples. -/
theorem outside_func_image_args
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (F : L.FuncSymbol)
    (a : Fin (L.funcArity F) → U)
    (b : Fin (L.funcArity F) → V)
    (hab : e ∘ a = b) :
    Structure.imageSet (outsideMap e hroot)
      {y : Outside ρA | y.1 ∈ A.func F a} =
      {z : Outside ρB | z.1 ∈ B.func F b} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have himg : e y.1 ∈ Structure.imageSet e (A.func F a) :=
      ⟨y.1, hy, rfl⟩
    rw [e.map_func F a, hab] at himg
    exact himg
  · intro hz
    have hz' : z.1 ∈ B.func F (e ∘ a) := by
      rw [hab]
      exact hz
    rw [← e.map_func F a] at hz'
    rcases hz' with ⟨y, hy, hey⟩
    have hyout : y ∉ Set.range ρA := by
      rintro ⟨r, hyr⟩
      subst y
      apply z.2
      refine ⟨r, ?_⟩
      exact (hroot r).symm.trans hey
    let yout : Outside ρA := ⟨y, hyout⟩
    refine ⟨yout, hy, ?_⟩
    apply Subtype.ext
    exact hey

/-- Special case for an all-moving input tuple. -/
theorem outside_func_image
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → Outside ρA) :
    Structure.imageSet (outsideMap e hroot)
      {y : Outside ρA | y.1 ∈ A.func F (Subtype.val ∘ x)} =
      {z : Outside ρB |
        z.1 ∈ B.func F (Subtype.val ∘ (outsideMap e hroot ∘ x))} := by
  apply outside_func_image_args e hroot F
    (Subtype.val ∘ x)
    (Subtype.val ∘ (outsideMap e hroot ∘ x))
  funext i
  rfl

/-- Splitting commutes with a root-compatible full embedding. -/
theorem split_embedding
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (a : U) :
    split ρB (e a) =
      sumMap (outsideMap e hroot) (split ρA a) := by
  apply unsplit_injective ρB
  rw [unsplit_split]
  cases hs : split ρA a with
  | inl r =>
      have hu := unsplit_split ρA a
      rw [hs] at hu
      change e a = ρB r
      rw [← hu]
      exact hroot r
  | inr x =>
      have hu := unsplit_split ρA a
      rw [hs] at hu
      change e a = e x.1
      exact congrArg e hu.symm

/-- A root-compatible strictly monotone full embedding induces a full
embedding of rooted moving encodings. -/
noncomputable def encodeEmbedding
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    [LinearOrder U] [LinearOrder V]
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A B)
    (hroot : ∀ r, e (ρA r) = ρB r)
    (hmono : StrictMono e) :
    Structure.Embedding (encode ρA) (encode ρB) where
  toFun := outsideMap e hroot
  injective := outsideMap_injective e hroot
  map_rel_iff := by
    intro Q x
    cases Q with
    | base S p =>
        have hfill := fill_map e hroot p x
        change
          B.rel S (Pattern.fill ρB p (outsideMap e hroot ∘ x)) ↔
            A.rel S (Pattern.fill ρA p x)
        rw [← hfill]
        exact e.map_rel_iff S (Pattern.fill ρA p x)
    | output F p r =>
        have hfill := fill_map e hroot p x
        change
          ρB r ∈ B.func F
              (Pattern.fill ρB p (outsideMap e hroot ∘ x)) ↔
            ρA r ∈ A.func F (Pattern.fill ρA p x)
        rw [← hfill]
        exact root_func_iff e hroot F (Pattern.fill ρA p x) r
    | cut r =>
        change ρB r < e (x 0).1 ↔ ρA r < (x 0).1
        rw [← hroot r]
        exact hmono.lt_iff_lt
  map_func := by
    intro Q x
    have hfill := fill_map e hroot Q.p
      (fun i => x i.castSucc)
    let argsA : Fin (L.funcArity Q.F) → Outside ρA :=
      fun i => x i.castSucc
    let argsB : Fin (L.funcArity Q.F) → Outside ρB :=
      outsideMap e hroot ∘ argsA
    have hfill' :
        e ∘ Pattern.fill ρA Q.p argsA =
          Pattern.fill ρB Q.p argsB := hfill
    change
      Structure.imageSet (outsideMap e hroot)
        {y : Outside ρA |
          y.1 ∈ A.func Q.F (Pattern.fill ρA Q.p argsA)} =
        {z : Outside ρB |
          z.1 ∈ B.func Q.F (Pattern.fill ρB Q.p argsB)}
    exact outside_func_image_args e hroot Q.F
      (Pattern.fill ρA Q.p argsA)
      (Pattern.fill ρB Q.p argsB) hfill'

/-- Ordered version of `encodeEmbedding`. -/
noncomputable def encodeOrderedEmbedding
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    [LinearOrder U] [LinearOrder V]
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A.withLinearOrder B.withLinearOrder)
    (hroot : ∀ r, e.linearOrderReduct (ρA r) = ρB r) :
    Structure.Embedding (encode ρA).withLinearOrder
      (encode ρB).withLinearOrder := by
  let f : Structure.Embedding (encode ρA) (encode ρB) :=
    encodeEmbedding e.linearOrderReduct hroot e.strictMono
  have hfmono : StrictMono f := by
    intro x y hxy
    exact e.strictMono hxy
  exact {
    toFun := f
    injective := f.injective
    map_func := f.map_func
    map_rel_iff := fun S x => by
      cases S with
      | inl S => exact f.map_rel_iff S x
      | inr r =>
          cases r
          change f (x (0 : Fin 2)) < f (x (1 : Fin 2)) ↔
            x (0 : Fin 2) < x (1 : Fin 2)
          exact hfmono.lt_iff_lt
  }

@[simp] theorem encodeOrderedEmbedding_apply
    {Root : Structure L R} {A : Structure L U} {B : Structure L V}
    [LinearOrder U] [LinearOrder V]
    {ρA : Structure.Embedding Root A}
    {ρB : Structure.Embedding Root B}
    (e : Structure.Embedding A.withLinearOrder B.withLinearOrder)
    (hroot : ∀ r, e.linearOrderReduct (ρA r) = ρB r)
    (x : Outside ρA) :
    encodeOrderedEmbedding e hroot x = outsideMap e.linearOrderReduct hroot x :=
  rfl

end StructuralRamsey.Rooted
