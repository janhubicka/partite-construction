import PartiteConstruction.Structure.FreeAmalgam
import Mathlib.Data.Fintype.Card

/-! # Finite free decompositions and free-amalgamation classes

For finite full structures, the universal side-localization definition of
irreducibility is equivalent to not being a free amalgam of two proper closed
substructures.  This is the finite decomposition fact used in the
Evans--Hubicka--Nesetril one-pass partite proof.

Consequently, a hereditary class closed under free amalgams is determined by
its irreducible members.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- The range of a full embedding is function-closed. -/
theorem Embedding.range_isClosed
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B) :
    B.IsClosed (Set.range e) := by
  intro F x hx y hy
  have hargs : ∀ i, ∃ a : U, e a = x i := by
    intro i
    exact hx i
  choose a ha using hargs
  have hxeq : e ∘ a = x := by
    funext i
    exact ha i
  have hy' : y ∈ B.func F (e ∘ a) := by
    rw [hxeq]
    exact hy
  rw [← e.map_func F a] at hy'
  rcases hy' with ⟨b, hb, hby⟩
  exact ⟨b, hby⟩

/-- Preimages of function-closed sets under full embeddings are closed. -/
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

/-- A concrete internal free decomposition into two proper closed
substructures. -/
structure ProperFreeDecomposition (A : Structure L U) where
  left : Set U
  right : Set U
  leftClosed : A.IsClosed left
  rightClosed : A.IsClosed right
  leftProper : left ≠ Set.univ
  rightProper : right ≠ Set.univ
  free :
    ∃ (H : Type v) (D : Structure L H)
      (sL : Embedding D (A.induce left leftClosed))
      (sR : Embedding D (A.induce right rightClosed)),
      IsFreeAmalgam sL sR
        (inclusion A left leftClosed)
        (inclusion A right rightClosed)

/-- Irreducibility rules out a proper internal free decomposition. -/
theorem Irreducible.noProperFreeDecomposition
    {A : Structure L U} (hA : A.Irreducible) :
    ¬ Nonempty (ProperFreeDecomposition A) := by
  rintro ⟨d⟩
  rcases d.free with ⟨H, D, sL, sR, hfree⟩
  have hside :=
    hA hfree (Embedding.id A)
  rcases hside with hleft | hright
  · apply d.leftProper
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨x, hx⟩ := hleft a
      change a = x.1 at hx
      rw [hx]
      exact x.2
  · apply d.rightProper
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨x, hx⟩ := hright a
      change a = x.1 at hx
      rw [hx]
      exact x.2

/-- Pull a crossing copy back through a free amalgam.  Its two side-preimages
give a proper internal free decomposition. -/
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
    have ha : a ∈ Lset := by rw [h]; exact Set.mem_univ a
    change e a ∈ Set.range iE at ha
    rcases ha with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  have hRproper : Rset ≠ Set.univ := by
    intro h
    apply hnotF
    intro a
    have ha : a ∈ Rset := by rw [h]; exact Set.mem_univ a
    change e a ∈ Set.range iF at ha
    rcases ha with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
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
        have hyr : y.1 ∈ Rset := by
          exact hRclosed F0 (Subtype.val ∘ x)
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
        have hyl : y.1 ∈ Lset := by
          exact hLclosed F0 (Subtype.val ∘ x)
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
        have huv : a.1 = b.1 := hab
        let z : Mset := ⟨a.1, ⟨a.2, by
          rw [huv]
          exact b.2⟩⟩
        refine ⟨z, ?_, ?_⟩
        · rfl
        · apply Subtype.ext
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
    free := ⟨Mset, AM, mL, mR, hInternal⟩
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
    by_cases hE : ∀ a : U, ∃ x : E, e a = iE x
    · exact Or.inl hE
    · by_cases hF : ∀ a : U, ∃ x : F, e a = iF x
      · exact Or.inr hF
      · exact (hnodecomp
          (properFreeDecomposition_of_crossing hfree e hE hF)).elim

/-- Subsingletons are irreducible in the free-amalgamation sense. -/
theorem irreducible_of_subsingleton
    (A : Structure L U) [Subsingleton U] :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  cases isEmpty_or_nonempty U with
  | inl hEmpty =>
      left
      intro a
      exact isEmptyElim a
  | inr hNonempty =>
      letI : Nonempty U := hNonempty
      let a0 : U := Classical.choice hNonempty
      rcases hfree.covers (e a0) with ⟨x, hx⟩ | ⟨x, hx⟩
      · left
        intro a
        refine ⟨x, ?_⟩
        rw [Subsingleton.elim a a0]
        exact hx
      · right
        intro a
        refine ⟨x, ?_⟩
        rw [Subsingleton.elim a a0]
        exact hx

/-- A carrier-polymorphic class of finite structures. -/
abbrev StructureClass (L : Language.{u}) :=
  ∀ {V : Type v}, Structure L V → Prop

/-- Heredity and closure under concrete free amalgams.  JEP is not needed for
the fixed-pair Ramsey theorem once A and B are members. -/
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

/-- Fintype version of the finite member test. -/
theorem mem_of_irreducibles_fintype
    {K : StructureClass (L := L)}
    (hK : FreeAmalgamationClass K)
    {A : Structure L U} [Fintype U]
    (hlocal :
      ∀ {X : Type v} (E : Structure L X), [Finite X] →
        E.Irreducible → Embedding E A → K E) :
    K A := by
  classical
  let P : (α : Type v) → [Fintype α] → Prop :=
    fun α _ =>
      ∀ (M : Structure L α),
        (∀ {X : Type v} (E : Structure L X), [Finite X] →
          E.Irreducible → Embedding E M → K E) →
        K M
  apply Fintype.induction_subsingleton_or_nontrivial (P := P) U
  · intro α inst hsub M hloc
    exact hloc M (irreducible_of_subsingleton M) (Embedding.id M)
  · intro α inst hnontr ih M hloc
    by_cases hIrr : M.Irreducible
    · exact hloc M hIrr (Embedding.id M)
    · have hdec : Nonempty (ProperFreeDecomposition M) := by
        by_contra hn
        exact hIrr
          ((irreducible_iff_noProperFreeDecomposition M).mpr hn)
      rcases hdec with ⟨d⟩
      let ML := M.induce d.left d.leftClosed
      let MR := M.induce d.right d.rightClosed
      letI : Fintype d.left := Fintype.ofFinite d.left
      letI : Fintype d.right := Fintype.ofFinite d.right
      have hleftOutside : ∃ x : α, x ∉ d.left := by
        by_contra hn
        push Not at hn
        apply d.leftProper
        ext x
        simp [hn x]
      obtain ⟨xl, hxl⟩ := hleftOutside
      have hrightOutside : ∃ x : α, x ∉ d.right := by
        by_contra hn
        push Not at hn
        apply d.rightProper
        ext x
        simp [hn x]
      obtain ⟨xr, hxr⟩ := hrightOutside
      have hleftCard :
          Fintype.card d.left < Fintype.card α :=
        Fintype.card_subtype_lt hxl
      have hrightCard :
          Fintype.card d.right < Fintype.card α :=
        Fintype.card_subtype_lt hxr
      have hML : K ML := by
        apply ih d.left hleftCard ML
        intro X E hX hE e
        let inc : Embedding ML M := inclusion M d.left d.leftClosed
        exact hloc E hX hE (inc.comp e)
      have hMR : K MR := by
        apply ih d.right hrightCard MR
        intro X E hX hE e
        let inc : Embedding MR M := inclusion M d.right d.rightClosed
        exact hloc E hX hE (inc.comp e)
      rcases d.free with ⟨H, D, sL, sR, hfree⟩
      exact hK.free hML hMR hfree

/-- A finite structure belongs to a hereditary free-amalgamation class as soon
as all its irreducible substructures do. -/
theorem mem_of_irreducibles
    {K : StructureClass (L := L)}
    (hK : FreeAmalgamationClass K)
    {A : Structure L U} [Finite U]
    (hlocal :
      ∀ {X : Type v} (E : Structure L X), [Finite X] →
        E.Irreducible → Embedding E A → K E) :
    K A := by
  letI : Fintype U := Fintype.ofFinite U
  exact hK.mem_of_irreducibles_fintype hlocal

end FreeAmalgamationClass

end StructuralRamsey.Structure
