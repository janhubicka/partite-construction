import PartiteConstruction.Ramsey.ClosureLocalFinitenessNoGo2019
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-! # Singleton vacuity in literal Definition 2.17(4b)

Every singleton induced relational structure is ordinarily irreducible,
hence intrinsically U-irreducible, even when it is not U-closed.
Consequently, if K has no one-element member, the literal (4b) premise
forces the entire candidate C to be empty. The copywise completion
conclusion then holds automatically, into the given B in K.

This uses the ORIGINAL IsUIrreducible, not the closed-test replacement.
No positive-power or rank-increment result is used. The theorem makes
the local-finiteness implication automatic for this kind of K; further
class/Ramsey data are needed for a full Theorem 2.18 counterexample.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W : Type v}

/-- A singleton is intrinsically U-irreducible independently of closures. -/
theorem singleton_isUIrreducible
    (rules : ClosureDescription L) (C : RelStructure L V) (x : V) :
    IsUIrreducible rules (C.induce {x}) := by
  have h : (C.induce {x}).Irreducible := by
    intro a b hab
    apply False.elim
    apply hab
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.2).trans
      (Set.mem_singleton_iff.mp b.2).symm
  exact h.isUIrreducible rules

/-- With no singleton in K, literal (4b) admits only empty candidates. -/
theorem isEmpty_of_intrinsic_tests_mem_of_no_singletons
    {rules : ClosureDescription L}
    {K : StructureClass.{u,v} (L := L)} (C : RelStructure L V)
    (hNoSingleton : ∀ {X : Type v} [Nonempty X] [Subsingleton X]
      (D : RelStructure L X), ¬ K D)
    (hAll : ∀ S : Set V,
      IsUIrreducible rules (C.induce S) → K (C.induce S)) :
    IsEmpty V := by
  constructor
  intro x
  let S : Set V := {x}
  letI : Nonempty S := ⟨⟨x, Set.mem_singleton x⟩⟩
  letI : Subsingleton S := ⟨by
    intro a b
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.2).trans
      (Set.mem_singleton_iff.mp b.2).symm⟩
  exact hNoSingleton (C.induce S)
    (hAll S (singleton_isUIrreducible rules C x))

/-- Literal (4b) alone implies the copy-completion conclusion when K
has no singleton members. Thus (4a), (4c), and the integer cutoff are
irrelevant for the corresponding local-finiteness implication. -/
theorem copywiseCompletion_of_intrinsic_tests_mem_of_no_singletons
    {rules : ClosureDescription L}
    {K : StructureClass.{u,v} (L := L)}
    (B : RelStructure L W) [Finite W] (hB : K B)
    (C : RelStructure L V)
    (hNoSingleton : ∀ {X : Type v} [Nonempty X] [Subsingleton X]
      (D : RelStructure L X), ¬ K D)
    (hAll : ∀ S : Set V,
      IsUIrreducible rules (C.induce S) → K (C.induce S)) :
    HasCopywiseCompletion K B C := by
  letI : IsEmpty V :=
    isEmpty_of_intrinsic_tests_mem_of_no_singletons C hNoSingleton hAll
  let f : V → W := fun x => isEmptyElim x
  refine ⟨W, inferInstance, B, hB, f, ?_⟩
  intro e
  refine ⟨Embedding.id B, ?_⟩
  intro b
  exact isEmptyElim (e b)

end StructuralRamsey.RelStructure
