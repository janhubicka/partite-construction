import PartiteConstruction.Structure.FreeAmalgam
import Mathlib.Data.Fintype.Card

/-! # Finite free decompositions and free-amalgamation classes

For finite full relation/function structures, the universal side-localization
definition of irreducibility is equivalent to saying that the structure is not
a free amalgam of two proper substructures.

This yields the standard finite closure principle used by the
Evans--Hubicka--Nesetril partite proof: in a hereditary class closed under free
amalgamation, a finite structure belongs to the class whenever all of its
irreducible substructures do.
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
  choose a ha using hx
  have hxeq : x = e ∘ a := by
    funext i
    exact (ha i).symm
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
    have h : e y ∈ imageSet e (A.func F x) := ⟨y, hy, rfl⟩
    rw [e.map_func F x] at h
    exact h
  exact hS F (e ∘ x) hx hey

/-- A free decomposition of A into two proper embedded sides. -/
structure ProperFreeDecomposition (A : Structure L U) where
  Common : Type v
  Left : Type v
  Right : Type v
  common : Structure L Common
  left : Structure L Left
  right : Structure L Right
  toLeft : Embedding common left
  toRight : Embedding common right
  leftIn : Embedding left A
  rightIn : Embedding right A
  free : IsFreeAmalgam toLeft toRight leftIn rightIn
  leftProper : ¬ Function.Surjective leftIn
  rightProper : ¬ Function.Surjective rightIn

/-- An irreducible structure has no proper free decomposition. -/
theorem Irreducible.noProperFreeDecomposition
    {A : Structure L U} (hA : A.Irreducible) :
    ¬ Nonempty (ProperFreeDecomposition A) := by
  rintro ⟨d⟩
  rcases hA d.free (Embedding.id A) with hleft | hright
  · apply d.leftProper
    intro a
    obtain ⟨x, hx⟩ := hleft a
    exact ⟨x, hx.symm⟩
  · apply d.rightProper
    intro a
    obtain ⟨x, hx⟩ := hright a
    exact ⟨x, hx.symm⟩

/-- If an embedded copy crosses both sides of a free amalgam, pulling the two
side ranges back along the embedding gives a proper free decomposition. -/
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
  have hLclosed : A.IsClosed Lset := e.preimage_isClosed LE hLE
  have hRclosed : A.IsClosed Rset := e.preimage_isClosed RF hRF
  have hLproper : ¬ Function.Surjective (inclusion A Lset hLclosed) := by
    intro hsurj
    apply hnotE
    intro a
    obtain ⟨x, hx⟩ := hsurj a
    have ha : e a ∈ LE := by
      change e a ∈ Set.range iE
      rw [← hx]
      exact x.2
    rcases ha with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  have hRproper : ¬ Function.Surjective (inclusion A Rset hRclosed) := by
    intro hsurj
    apply hnotF
    intro a
    obtain ⟨x, hx⟩ := hsurj a
    have ha : e a ∈ RF := by
      change e a ∈ Set.range iF
      rw [← hx]
      exact x.2
    rcases ha with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
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
      rcases hfree.covers (e a) with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact Or.inl ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have huv : a.1 = b.1 := congrArg Subtype.val hab
        let z : Mset := ⟨a.1, ⟨a.2, by simpa [huv] using b.2⟩⟩
        refine ⟨z, rfl, ?_⟩
        apply Subtype.ext
        exact huv.symm
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
          have h : e y ∈ imageSet e (A.func F0 x) := ⟨y, hy, rfl⟩
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
    by_contra hside
    simp only [not_or, not_forall] at hside
    rcases hside with ⟨⟨aE, hE⟩, ⟨aF, hF⟩⟩
    have hnotE : ¬ ∀ a : U, ∃ x : E, e a = iE x := by
      intro h
      rcases h aE with ⟨x, hx⟩
      exact hE x hx
    have hnotF : ¬ ∀ a : U, ∃ x : F, e a = iF x := by
      intro h
      rcases h aF with ⟨x, hx⟩
      exact hF x hx
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
      ∀ {X : Type v} [Finite X], ∀ E : Structure L X,
        E.Irreducible → Embedding E A → K E) :
    K A := by
  classical
  let aux :
      ∀ n : ℕ, ∀ {X : Type v} [Fintype X] (E : Structure L X),
        Fintype.card X = n →
        (∀ {Y : Type v} [Finite Y], ∀ F : Structure L Y,
          F.Irreducible → Embedding F E → K F) →
        K E := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X instX E hcard hloc
        by_cases hIrr : E.Irreducible
        · exact hloc E hIrr (Embedding.id E)
        · have hdec : Nonempty (ProperFreeDecomposition E) := by
            by_contra hn
            exact hIrr ((irreducible_iff_noProperFreeDecomposition E).mpr hn)
          rcases hdec with ⟨d⟩
          letI : Finite d.Left :=
            Finite.of_injective d.leftIn d.leftIn.injective
          letI : Finite d.Right :=
            Finite.of_injective d.rightIn d.rightIn.injective
          letI : Fintype d.Left := Fintype.ofFinite d.Left
          letI : Fintype d.Right := Fintype.ofFinite d.Right
          have hleftCard : Fintype.card d.Left < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.leftIn d.leftIn.injective d.leftProper
          have hrightCard : Fintype.card d.Right < n := by
            rw [← hcard]
            exact Fintype.card_lt_of_injective_not_surjective
              d.rightIn d.rightIn.injective d.rightProper
          have hLeft : K d.left := by
            apply ih (Fintype.card d.Left) hleftCard
              d.left rfl
            intro Y _ F hF eF
            exact hloc F hF (d.leftIn.comp eF)
          have hRight : K d.right := by
            apply ih (Fintype.card d.Right) hrightCard
              d.right rfl
            intro Y _ F hF eF
            exact hloc F hF (d.rightIn.comp eF)
          exact hK.free hLeft hRight d.free
  letI : Fintype U := Fintype.ofFinite U
  exact aux (Fintype.card U) A rfl hlocal

end FreeAmalgamationClass

end StructuralRamsey.Structure
