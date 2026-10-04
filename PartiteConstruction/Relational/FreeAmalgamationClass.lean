import PartiteConstruction.Iterated.LocalTreeLike
import Mathlib.Data.Fintype.Card

/-! # Finite relational free-amalgamation classes

This file isolates the class-theoretic step used in the
Evans--Hubicka--Nesetril Ramsey theorem.  For finite relational structures,
membership in a hereditary class closed under free amalgamation is determined
by the irreducible induced substructures.

The proof is deliberately independent of orders and Ramsey theory so the
result can be reused by applications such as the high-girth development.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- A carrier-polymorphic class of finite relational structures. -/
abbrev StructureClass (L : RelLanguage.{u}) :=
  ∀ {V : Type v}, RelStructure L V → Prop

/-- Hereditary closure and closure under concrete free amalgams.

JEP is not needed for the fixed-target Ramsey argument, so it is not included
in this minimal interface. -/
structure FreeAmalgamationClass
    (K : StructureClass (L := L)) : Prop where
  hereditary :
    ∀ {V W : Type v} {A : RelStructure L V} {B : RelStructure L W},
      K B → Embedding A B → K A
  free :
    ∀ {H E F C : Type v}
      {D : RelStructure L H} {A : RelStructure L E}
      {B : RelStructure L F} {Cstr : RelStructure L C}
      {sA : Embedding D A} {sB : Embedding D B}
      {iA : Embedding A Cstr} {iB : Embedding B Cstr},
      K A → K B → IsFreeAmalgam sA sB iA iB → K Cstr

/-- A decomposition of a relational structure as a free amalgam of two proper
induced substructures. -/
structure ProperFreeDecomposition (A : RelStructure L U) where
  Common : Type v
  Left : Type v
  Right : Type v
  common : RelStructure L Common
  left : RelStructure L Left
  right : RelStructure L Right
  toLeft : Embedding common left
  toRight : Embedding common right
  leftIn : Embedding left A
  rightIn : Embedding right A
  free : IsFreeAmalgam toLeft toRight leftIn rightIn
  leftProper : ¬ Function.Surjective leftIn
  rightProper : ¬ Function.Surjective rightIn

/-- A non-irreducible relational structure splits as a free amalgam of two
proper induced substructures: delete one vertex of a separated pair on each
side. -/
theorem properFreeDecomposition_of_not_irreducible
    {A : RelStructure L U} (hA : ¬ A.Irreducible) :
    Nonempty (ProperFreeDecomposition A) := by
  classical
  have hpair :
      ∃ a b : U, a ≠ b ∧
        ¬ ∃ (R : L.Symbol) (z : Fin (L.arity R) → U)
          (i j : Fin (L.arity R)),
            A.rel R z ∧ z i = a ∧ z j = b := by
    by_contra h
    push_neg at h
    apply hA
    intro a b hab
    exact h a b hab
  rcases hpair with ⟨a, b, hab, hsep⟩
  let Lset : Set U := {x | x ≠ b}
  let Rset : Set U := {x | x ≠ a}
  let Mset : Set U := Lset ∩ Rset
  let AL := A.induce Lset
  let AR := A.induce Rset
  let AM := A.induce Mset
  let mL : Embedding AM AL := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let mR : Embedding AM AR := {
    toFun := fun x => ⟨x.1, x.2.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let iL : Embedding AL A := inclusion A Lset
  let iR : Embedding AR A := inclusion A Rset
  have hLproper : ¬ Function.Surjective iL := by
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj b
    have hxval : x.1 = b := by
      simpa [iL] using hx
    exact x.2 hxval
  have hRproper : ¬ Function.Surjective iR := by
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj a
    have hxval : x.1 = a := by
      simpa [iR] using hx
    exact x.2 hxval
  have hfree : IsFreeAmalgam mL mR iL iR := by
    constructor
    · intro x
      by_cases hxb : x = b
      · refine Or.inr ⟨⟨x, ?_⟩, ?_⟩
        · simpa [hxb] using hab.symm
        · rfl
      · exact Or.inl ⟨⟨x, hxb⟩, rfl⟩
    · intro x y
      constructor
      · intro hxy
        have hval : x.1 = y.1 := by
          simpa [iL, iR] using hxy
        let z : Mset := ⟨x.1, ⟨x.2, by simpa [hval] using y.2⟩⟩
        refine ⟨z, ?_, ?_⟩
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          exact hval
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        by_cases hleft : ∀ k, z k ≠ b
        · let zl : Fin (L.arity R) → Lset :=
            fun k => ⟨z k, hleft k⟩
          exact Or.inl ⟨zl, hz, rfl⟩
        · push_neg at hleft
          obtain ⟨j, hj⟩ := hleft
          have hright : ∀ k, z k ≠ a := by
            intro k hk
            apply hsep
            exact ⟨R, z, k, j, hz, hk, hj⟩
          let zr : Fin (L.arity R) → Rset :=
            fun k => ⟨z k, hright k⟩
          exact Or.inr ⟨zr, hz, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
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
    free := hfree
    leftProper := hLproper
    rightProper := hRproper
  }⟩

namespace FreeAmalgamationClass

/-- A finite member test: a hereditary relational free-amalgamation class is
determined by its irreducible induced substructures. -/
theorem mem_of_irreducibles
    {K : StructureClass (L := L)}
    (hK : FreeAmalgamationClass K)
    {A : RelStructure L U} [Finite U]
    (hlocal :
      ∀ {X : Type v} [Finite X], ∀ E : RelStructure L X,
        E.Irreducible → Embedding E A → K E) :
    K A := by
  classical
  let aux :
      ∀ n : ℕ, ∀ {X : Type v} [Fintype X] (E : RelStructure L X),
        Fintype.card X = n →
        (∀ {Y : Type v} [Finite Y], ∀ F : RelStructure L Y,
          F.Irreducible → Embedding F E → K F) →
        K E := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X instX E hcard hloc
        by_cases hIrr : E.Irreducible
        · exact hloc E hIrr (Embedding.id E)
        · rcases properFreeDecomposition_of_not_irreducible hIrr with ⟨d⟩
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
            apply ih (Fintype.card d.Left) hleftCard d.left rfl
            intro Y _ F hF eF
            exact hloc F hF (d.leftIn.comp eF)
          have hRight : K d.right := by
            apply ih (Fintype.card d.Right) hrightCard d.right rfl
            intro Y _ F hF eF
            exact hloc F hF (d.rightIn.comp eF)
          exact hK.free hLeft hRight d.free
  letI : Fintype U := Fintype.ofFinite U
  exact aux (Fintype.card U) A rfl hlocal

end FreeAmalgamationClass

end StructuralRamsey.RelStructure
