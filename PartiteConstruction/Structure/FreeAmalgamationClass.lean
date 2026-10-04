import PartiteConstruction.Structure.FreeAmalgam

/-! # Finite free decompositions and free-amalgamation classes

For finite full structures, the universal side-localization definition of
irreducibility is equivalent to not being a free amalgam of two proper closed
substructures.  This is the finite decomposition fact used in the
Evans--Hubicka--Nesetril one-pass partite proof.

As a consequence, a hereditary class closed under concrete free amalgams is
determined by its irreducible members: if every irreducible substructure of a
finite structure belongs to the class, then the whole structure belongs.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- The range of a full embedding is closed under all function values. -/
theorem Embedding.range_isClosed
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B) :
    B.IsClosed (Set.range e) := by
  intro F x hx y hy
  have hargs : ∀ i, ∃ a : U, x i = e a := hx
  choose a ha using hargs
  have hxeq : x = e ∘ a := by
    funext i
    exact ha i
  subst x
  rw [← e.map_func F a] at hy
  rcases hy with ⟨b, hb, rfl⟩
  exact ⟨b, rfl⟩

/-- The inverse image of a closed set under a full embedding is closed. -/
theorem Embedding.preimage_isClosed
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B) (S : Set V)
    (hS : B.IsClosed S) :
    A.IsClosed {a | e a ∈ S} := by
  intro F x hx y hy
  have hey : e y ∈ B.func F (e ∘ x) := by
    have h :
        e y ∈ Structure.imageSet e (A.func F x) :=
      ⟨y, hy, rfl⟩
    rw [e.map_func F x] at h
    exact h
  exact hS F (e ∘ x) hx hey

/-- A concrete internal free decomposition of A into two proper closed
substructures. -/
structure ProperFreeDecomposition (A : Structure L U) where
  left : Set U
  right : Set U
  leftClosed : A.IsClosed left
  rightClosed : A.IsClosed right
  leftProper : left ≠ Set.univ
  rightProper : right ≠ Set.univ
  free :
    let meet : Set U := left ∩ right
    let meetClosed : A.IsClosed meet := by
      intro F x hx y hy
      exact ⟨
        leftClosed F x (fun i => (hx i).1) hy,
        rightClosed F x (fun i => (hx i).2) hy⟩
    IsFreeAmalgam
      (inclusion (A.induce left leftClosed) meet
        (by
          intro F x hx y hy
          exact ⟨leftClosed F (Subtype.val ∘ x)
            (fun i => (x i).2) hy, rightClosed F
            (Subtype.val ∘ x) (fun i => (hx i).2) hy⟩))
      (inclusion (A.induce right rightClosed) meet
        (by
          intro F x hx y hy
          exact ⟨leftClosed F (Subtype.val ∘ x)
            (fun i => (hx i).1) hy, rightClosed F
            (Subtype.val ∘ x) (fun i => (x i).2) hy⟩))
      (inclusion A left leftClosed)
      (inclusion A right rightClosed)

/-- An irreducible finite structure has no proper internal free
decomposition. -/
theorem Irreducible.noProperFreeDecomposition
    {A : Structure L U} (hA : A.Irreducible) :
    ¬ Nonempty (ProperFreeDecomposition A) := by
  rintro ⟨d⟩
  let meet : Set U := d.left ∩ d.right
  let meetClosed : A.IsClosed meet := by
    intro F x hx y hy
    exact ⟨
      d.leftClosed F x (fun i => (hx i).1) hy,
      d.rightClosed F x (fun i => (hx i).2) hy⟩
  have hside :=
    hA d.free (Embedding.id A)
  rcases hside with hleft | hright
  · apply d.leftProper
    ext a
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨x, hx⟩ := hleft a
      exact congrArg Subtype.val hx.symm ▸ x.2
  · apply d.rightProper
    ext a
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨x, hx⟩ := hright a
      exact congrArg Subtype.val hx.symm ▸ x.2

/-- If an embedded copy crosses both sides of a free amalgam, pulling the two
side ranges back along the embedding gives a proper internal free
decomposition. -/
theorem properFreeDecomposition_of_crossing
    {A : Structure L U}
    {H E F C : Type v}
    {Dsrc : Structure L H} {Esrc : Structure L E}
    {Fsrc : Structure L F} {Csrc : Structure L C}
    {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
    {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding A Csrc)
    (hnotE : ¬ ∀ a : U, ∃ x : E, e a = iE x)
    (hnotF : ¬ ∀ a : U, ∃ x : F, e a = iF x) :
    Nonempty (ProperFreeDecomposition A) := by
  classical
  let LE : Set C := Set.range iE
  let RF : Set C := Set.range iF
  have hLE : Csrc.IsClosed LE := iE.range_isClosed
  have hRF : Csrc.IsClosed RF := iF.range_isClosed
  let Lset : Set U := {a | e a ∈ LE}
  let Rset : Set U := {a | e a ∈ RF}
  have hLclosed : A.IsClosed Lset :=
    e.preimage_isClosed LE hLE
  have hRclosed : A.IsClosed Rset :=
    e.preimage_isClosed RF hRF
  have hLproper : Lset ≠ Set.univ := by
    intro h
    apply hnotE
    intro a
    have ha : a ∈ Lset := by rw [h]; trivial
    exact ha
  have hRproper : Rset ≠ Set.univ := by
    intro h
    apply hnotF
    intro a
    have ha : a ∈ Rset := by rw [h]; trivial
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
    injective := by intro x y h; exact Subtype.ext (congrArg Subtype.val h)
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
    injective := by intro x y h; exact Subtype.ext (congrArg Subtype.val h)
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
      rcases hfree.covers (e a) with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact Or.inl ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have huv : a.1 = b.1 := congrArg Subtype.val hab
        let z : Mset := ⟨a.1, ⟨a.2, by simpa [huv] using b.2⟩⟩
        exact ⟨z, rfl, by apply Subtype.ext; exact huv.symm⟩
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        have hez : Csrc.rel R (e ∘ z) :=
          (e.map_rel_iff R z).mpr hz
        rcases (hfree.rel_iff R (e ∘ z)).mp hez with
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
        have hey : e y ∈ Csrc.func F0 (e ∘ x) := by
          have h :
              e y ∈ Structure.imageSet e (A.func F0 x) :=
            ⟨y, hy, rfl⟩
          rw [e.map_func F0 x] at h
          exact h
        rcases (hfree.func_iff F0 (e ∘ x) (e y)).mp hey with
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
  refine ⟨{
    left := Lset
    right := Rset
    leftClosed := hLclosed
    rightClosed := hRclosed
    leftProper := hLproper
    rightProper := hRproper
    free := ?_
  }⟩
  simpa [Mset, AL, AR, AM, mL, mR, iL, iR] using hInternal

/-- For finite structures the universal side-localization notion is equivalent
to the classical EHN definition: not a free amalgam of two proper
substructures. -/
theorem irreducible_iff_noProperFreeDecomposition
    (A : Structure L U) :
    A.Irreducible ↔ ¬ Nonempty (ProperFreeDecomposition A) := by
  constructor
  · exact Irreducible.noProperFreeDecomposition
  · intro hnodecomp
    intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
    by_contra h
    push Not at h
    rcases h with ⟨hnotE, hnotF⟩
    exact hnodecomp
      (properFreeDecomposition_of_crossing hfree e hnotE hnotF)

/-- A carrier-polymorphic class of finite L-structures. -/
abbrev StructureClass (L : Language.{u}) :=
  ∀ {V : Type v}, Structure L V → Prop

/-- Hereditary closure and closure under concrete free amalgams.  This is the
part of the usual free-amalgamation-class axioms used by the Ramsey proof;
JEP is not needed once A and B are fixed members. -/
structure FreeAmalgamationClass
    (K : StructureClass (L := L)) : Prop where
  hereditary :
    ∀ {V W : Type v} {A : Structure L V} {B : Structure L W},
      K B → Embedding A B → K A
  free :
    ∀ {H E F C : Type v}
      {D : Structure L H} {A : Structure L E}
      {B : Structure L F} {Cstr : Structure L C}
      {sA : Embedding D A} {sB : Embedding D B}
      {iA : Embedding A Cstr} {iB : Embedding B Cstr},
      K A → K B → IsFreeAmalgam sA sB iA iB → K Cstr

namespace FreeAmalgamationClass

/-- A finite member test: hereditary free-amalgamation classes are determined
by their irreducible substructures. -/
theorem mem_of_irreducibles
    {K : StructureClass (L := L)}
    (hK : FreeAmalgamationClass K)
    {A : Structure L U} [Finite U]
    (hlocal :
      ∀ {X : Type v} (E : Structure L X), [Finite X] →
        E.Irreducible → Embedding E A → K E) :
    K A := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  -- Strong induction on the carrier cardinality.
  induction hcard : Fintype.card U using Nat.strong_induction_on generalizing U A with
  | h n ih =>
      by_cases hIrr : A.Irreducible
      · exact hlocal A hIrr (Embedding.id A)
      · have hdec :
          Nonempty (ProperFreeDecomposition A) := by
          by_contra hn
          exact hIrr ((irreducible_iff_noProperFreeDecomposition A).mpr hn)
        rcases hdec with ⟨d⟩
        let AL := A.induce d.left d.leftClosed
        let AR := A.induce d.right d.rightClosed
        letI : Fintype d.left := Fintype.ofFinite d.left
        letI : Fintype d.right := Fintype.ofFinite d.right
        have hleftCard : Fintype.card d.left < n := by
          rw [← hcard]
          apply Fintype.card_lt_iff.mpr
          refine ⟨Subtype.val, Subtype.val_injective, ?_⟩
          intro hsurj
          apply d.leftProper
          ext a
          constructor
          · intro _; trivial
          · intro _
            obtain ⟨x, hx⟩ := hsurj a
            exact congrArg Subtype.val hx ▸ x.2
        have hrightCard : Fintype.card d.right < n := by
          rw [← hcard]
          apply Fintype.card_lt_iff.mpr
          refine ⟨Subtype.val, Subtype.val_injective, ?_⟩
          intro hsurj
          apply d.rightProper
          ext a
          constructor
          · intro _; trivial
          · intro _
            obtain ⟨x, hx⟩ := hsurj a
            exact congrArg Subtype.val hx ▸ x.2
        have hAL : K AL := by
          apply ih (Fintype.card d.left) hleftCard rfl
          intro X E hX hE e
          let inc : Embedding AL A := inclusion A d.left d.leftClosed
          exact hlocal E hX hE (inc.comp e)
        have hAR : K AR := by
          apply ih (Fintype.card d.right) hrightCard rfl
          intro X E hX hE e
          let inc : Embedding AR A := inclusion A d.right d.rightClosed
          exact hlocal E hX hE (inc.comp e)
        exact hK.free hAL hAR d.free

end FreeAmalgamationClass

end StructuralRamsey.Structure
