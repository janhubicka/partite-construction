import PartiteConstruction.Functional.WholeMaskWeakDomainUnaryExample2019
import PartiteConstruction.Functional.WholeMaskWeakDomainObstruction2019

/-!
# Intrinsic full weak completion does not imply relative OLD K-completion

The two-vertex unary source F(0)=some {1}, F(1)=none has a whole-fibre
weak restriction to S={0} where the operation becomes undefined.
That weak genuine partial-function source admits a FULL embedding
into the one-point all-undefined target.

Nevertheless its AMBIENT induced OLD complete-mask relational graph
retains the active F-domain at 0. Thus there is NO positive OLD
homomorphism at all from that exact induced tagged-free source into
the canonical OLD graph of the very same one-point undefined target.

This is a witnessed gap in the OTHER logical direction from PR #524:
even an intrinsic weak FULL functional embedding does not certify
the ambient-relative K-completion map required by the 2019 profile
sparsening construction. The stronger tagged map is impossible since
it would restrict to such an OLD homomorphism.

The example does NOT refute the corrected relational Theorem 2.18
or its genuine partial Ramsey-arrow corollary. It demonstrates that
one may not derive the missing relative local K-class axiom merely
from the old intrinsic-weak full embedding premise.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

private def unaryWeakCarrier : Set (Fin 2) := {(0 : Fin 2)}

/-- The weak source in the two-vertex unary example REALLY has a
full genuine partial-function embedding into a singleton structure
where the unary operation is undefined. All function domain bits
match on the WEAK source, and the map is injective. -/
noncomputable def weakDomainUnaryToy_fullWeakToUndefined :
    Embedding (wholeWeakInduce weakDomainUnaryToy unaryWeakCarrier)
      undefinedExample where
  toFun := fun _ => ()
  injective := by
    intro x y _
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).trans
      (Set.mem_singleton_iff.mp y.2).symm
  map_rel_iff := by
    intro R
    exact Empty.elim R
  map_func := by
    intro F xs
    cases F
    have hx : (xs (0 : Fin 1)).1 = (0 : Fin 2) :=
      Set.mem_singleton_iff.mp (xs 0).2
    have hValue :
        weakDomainUnaryToy.func ()
          (Subtype.val ∘ xs) =
          some ({(1 : Fin 2)} : Set (Fin 2)) := by
      change (if (xs (0 : Fin 1)).1 = 0
        then some ({(1 : Fin 2)} : Set (Fin 2))
        else none) = _
      simp [hx]
    change
      (wholeWeakValue unaryWeakCarrier
        (weakDomainUnaryToy.func () (Subtype.val ∘ xs))).map
          (StructuralRamsey.Structure.imageSet (fun _ => ())) =
        none
    rw [hValue]
    rw [wholeWeakValue_of_not_subset unaryWeakCarrier
      ({(1 : Fin 2)} : Set (Fin 2))
      weakDomainUnaryToy_lost]
    rfl

/-- No ambient exact OLD homomorphism to the SAME canonical singleton
undefined target exists, despite the preceding FULL functional weak
embedding. Its retained source domain relation would have to map to
a target with a defined operation. -/
theorem weakDomainUnaryToy_no_oldHomToUndefined
    (f : unaryWeakCarrier → Unit) :
    ¬ ((weakDomainUnaryToy.wholeMaskPatternGraph
        (fun x : Fin 2 => x)).induce unaryWeakCarrier).IsHomomorphism
      (undefinedExample.wholeMaskPatternGraph
        (fun _ : Unit => ())) f := by
  intro hf
  let xs : Fin 1 → unaryWeakCarrier := fun _ =>
    ⟨0, by simp [unaryWeakCarrier]⟩
  have hTrTarget : FibreTransversal undefinedExample
      (fun _ : Unit => ()) := by
    intro F ys U hVal y hy z hz heq
    cases hVal
  have hTarget : undefinedExample.Defined () (f ∘ xs) :=
    oldInducedHom_target_defined_of_ambient_defined
      weakDomainUnaryToy (fun x : Fin 2 => x)
      weakDomainUnaryToy_transversal
      unaryWeakCarrier undefinedExample
      (fun _ : Unit => ()) hTrTarget
      f hf () xs
      ⟨{(1 : Fin 2)}, by
        change weakDomainUnaryToy.func ()
          (fun _ : Fin 1 => (0 : Fin 2)) = _
        exact weakDomainUnaryToy_value⟩
  obtain ⟨T,hT⟩ := hTarget
  cases hT

/-- A concrete FULL intrinsic weak function completion fails to yield
an ambient OLD local homomorphism into its target, even if one
forgets all 2019 fresh closure tags. -/
theorem weakDomainUnaryToy_fullWeak_but_noOldRelativeCompletion :
    Nonempty (Embedding
      (wholeWeakInduce weakDomainUnaryToy unaryWeakCarrier)
      undefinedExample) ∧
    ¬ ∃ f : unaryWeakCarrier → Unit,
      ((weakDomainUnaryToy.wholeMaskPatternGraph
          (fun x : Fin 2 => x)).induce unaryWeakCarrier).IsHomomorphism
        (undefinedExample.wholeMaskPatternGraph
          (fun _ : Unit => ())) f :=
  ⟨⟨weakDomainUnaryToy_fullWeakToUndefined⟩,
    fun ⟨f,hf⟩ => weakDomainUnaryToy_no_oldHomToUndefined f hf⟩

end StructuralRamsey.PartialSetStructure
