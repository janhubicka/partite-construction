import PartiteConstruction.Functional.EHNIrreducibleInputCoverRootReroot
import PartiteConstruction.Functional.EHNGlobalDefectDecomposition

/-!
# Track D: all non-full EHN defects occur across irreducible source charts

The merged input-cover criterion is sufficient to reflect old relation and
function domains. Here is its pointwise converse with ACTUAL source tuples:
each specific reflection failure avoids EVERY full irreducible source test
containing all its inputs. Likewise two colliding EHN labels cannot coexist
inside any full irreducible source test.

Consequently every non-full EHN projection has one of three precisely
SOURCE-MATCHED cross-chart defects, with no source finiteness premise.

This is not the history-compatible relative strict B-tree completion for
maximal Hales--Jewett mixed tests. Full irreducible source charts can have
extra target-image overlaps, and a decomposition of a diagnostic input
hull does not decrease the whole exact weak-test generator rank.
The numbered survey manuscript stays frozen.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Colliding EHN labels of distinct actual source vertices cannot both
belong to ANY full irreducible function-closed source test.
The source chart, not merely an individual active input hull, is arbitrary. -/
theorem IsEHNHomomorphismEmbedding.collision_outside_every_irreducible_chart
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (x y : U) (hDistinct : x ≠ y) (hCollision : p x = p y)
    (S : Set U) (hS : C.IsClosed S)
    (hIrr : (C.induce S hS).Irreducible) :
    ¬ (x ∈ S ∧ y ∈ S) := by
  rintro ⟨hx, hy⟩
  let Small := C.induce S hS
  let inc : Embedding Small C := inclusion C S hS
  obtain ⟨e, he⟩ := hp.2 Small hIrr inc
  have hSubtype : (⟨x, hx⟩ : S) = (⟨y, hy⟩ : S) := by
    apply e.injective
    calc
      e ⟨x, hx⟩ = p x := he ⟨x, hx⟩
      _ = p y := hCollision
      _ = e ⟨y, hy⟩ := (he ⟨y, hy⟩).symm
  exact hDistinct (congrArg Subtype.val hSubtype)

/-- Any target-only OLD relation on an ORIGINAL source input tuple is
absent from every full irreducible source chart containing ALL its inputs.
It is essential that the tuple may be source-NEGATIVE. -/
theorem IsEHNHomomorphismEmbedding.relation_failure_outside_every_irreducible_chart
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (R : L.RelSymbol) (xs : Fin (L.relArity R) → U)
    (hTarget : D.rel R (p ∘ xs))
    (hSource : ¬ C.rel R xs)
    (S : Set U) (hS : C.IsClosed S)
    (hIrr : (C.induce S hS).Irreducible) :
    ¬ (∀ i, xs i ∈ S) := by
  intro hInputs
  let Small := C.induce S hS
  let inc : Embedding Small C := inclusion C S hS
  obtain ⟨e, he⟩ := hp.2 Small hIrr inc
  let q : Fin (L.relArity R) → S :=
    fun i => ⟨xs i, hInputs i⟩
  have hEq : e ∘ q = p ∘ xs := by
    funext i
    exact he (q i)
  have hTarget' : D.rel R (e ∘ q) := by
    rw [hEq]
    exact hTarget
  have hSmall : Small.rel R q := (e.map_rel_iff R q).mp hTarget'
  apply hSource
  change C.rel R (Subtype.val ∘ q) at hSmall
  have hq : Subtype.val ∘ q = xs := by
    funext i
    rfl
  rw [hq] at hSmall
  exact hSmall

/-- Every target-defined/source-undefined function input defect must
cross the actual full irreducible source chart cover.
There is no independent extra-output defect on SOURCE-DEFINED tuples:
that is already excluded by EHN fibre exactness. -/
theorem IsEHNHomomorphismEmbedding.domain_failure_outside_every_irreducible_chart
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
    (hTarget : (D.func F (p ∘ xs)).Nonempty)
    (hSource : ¬ (C.func F xs).Nonempty)
    (S : Set U) (hS : C.IsClosed S)
    (hIrr : (C.induce S hS).Irreducible) :
    ¬ (∀ i, xs i ∈ S) := by
  intro hInputs
  let Small := C.induce S hS
  let inc : Embedding Small C := inclusion C S hS
  obtain ⟨e, he⟩ := hp.2 Small hIrr inc
  let q : Fin (L.funcArity F) → S :=
    fun i => ⟨xs i, hInputs i⟩
  have hEq : e ∘ q = p ∘ xs := by
    funext i
    exact he (q i)
  obtain ⟨y, hy⟩ := hTarget
  have hTarget' : y ∈ D.func F (e ∘ q) := by
    rw [hEq]
    exact hy
  have himg : y ∈ imageSet e (Small.func F q) := by
    rw [e.map_func F q]
    exact hTarget'
  obtain ⟨z, hz, _⟩ := himg
  apply hSource
  refine ⟨z.1, ?_⟩
  change z.1 ∈ C.func F (Subtype.val ∘ q) at hz
  have hq : Subtype.val ∘ q = xs := by
    funext i
    rfl
  rw [hq] at hz
  exact hz

/-- Every non-full EHN projection has a concrete cross-chart defect,
with an ACTUAL original source tuple in the two input cases.
No finite-source or global all-input-cover assumption is required.
The conclusion is source geometry, NOT relative target-tree completion. -/
theorem IsEHNHomomorphismEmbedding.nonFull_crossChart_trichotomy
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hNoFull : ¬ ∃ e : Embedding C D, ∀ x : U, e x = p x) :
    (∃ x y : U, x ≠ y ∧ p x = p y ∧
      ∀ (S : Set U) (hS : C.IsClosed S),
        (C.induce S hS).Irreducible → ¬ (x ∈ S ∧ y ∈ S)) ∨
    (∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
      D.rel R (p ∘ xs) ∧ ¬ C.rel R xs ∧
      ∀ (S : Set U) (hS : C.IsClosed S),
        (C.induce S hS).Irreducible → ¬ (∀ i, xs i ∈ S)) ∨
    (∃ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U),
      (D.func F (p ∘ xs)).Nonempty ∧
      ¬ (C.func F xs).Nonempty ∧
      ∀ (S : Set U) (hS : C.IsClosed S),
        (C.induce S hS).Irreducible → ¬ (∀ i, xs i ∈ S)) := by
  rcases hp.nonFull_exactThreeDefects hNoFull with
      ⟨x, y, hDistinct, hEq⟩ |
      ⟨R, xs, hTarget, hSource⟩ |
      ⟨F, xs, hTarget, hSource⟩
  · exact Or.inl ⟨x, y, hDistinct, hEq,
      fun S hS hIrr =>
        hp.collision_outside_every_irreducible_chart
          x y hDistinct hEq S hS hIrr⟩
  · exact Or.inr (Or.inl ⟨R, xs, hTarget, hSource,
      fun S hS hIrr =>
        hp.relation_failure_outside_every_irreducible_chart
          R xs hTarget hSource S hS hIrr⟩)
  · exact Or.inr (Or.inr ⟨F, xs, hTarget, hSource,
      fun S hS hIrr =>
        hp.domain_failure_outside_every_irreducible_chart
          F xs hTarget hSource S hS hIrr⟩)

end StructuralRamsey.Structure
