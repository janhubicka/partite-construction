import PartiteConstruction.Functional.PartialDomainGraphClosedRange2019
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track C: full rich partial embedding factors through its exact closed image

The English second-cover proof composes a native full E-copy with
a full OLD completion of its actual image q[E]. Replacing that
exact image by a closure hull may exceed the n-vertex budget.

Every full genuine Option(Set) embedding has a genuinely
function-closed range (already verified in the domain/output
graph dictionary), including defined-empty applications.
Here we factor it through the actual induced structure on
its literal range, retaining the same source and vertex map.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {U : Type v} {V : Type w}

/-- A full genuinely partial embedding factors through the genuinely
induced full substructure of its own EXACT range. The source carrier
and vertex map are unchanged, with complete Option-valued laws. -/
noncomputable def Embedding.codRestrictClosedRange
    {A : PartialSetStructure L U} {B : PartialSetStructure L V}
    (e : Embedding A B) :
    Embedding A
      (B.induceClosed (Set.range e.toFun) e.range_isClosed) := by
  classical
  let R : Set V := Set.range e.toFun
  let hR : B.IsClosed R := e.range_isClosed
  let eRange : U → R := fun x => ⟨e.toFun x, ⟨x, rfl⟩⟩
  refine {
    toFun := eRange
    injective := ?_
    map_rel_iff := ?_
    map_func := ?_
  }
  · intro x y h
    apply e.injective
    exact congrArg Subtype.val h
  · intro F xs
    change B.rel F (e.toFun ∘ xs) ↔ A.rel F xs
    exact e.map_rel_iff F xs
  · intro F xs
    change
      (A.func F xs).map (Structure.imageSet eRange) =
      (B.func F (e.toFun ∘ xs)).map
        (fun Q : Set V => {y : R | y.1 ∈ Q})
    cases hA : A.func F xs with
    | none =>
        have hB : B.func F (e.toFun ∘ xs) = none := by
          simpa only [hA, Option.map_none] using (e.map_func F xs).symm
        simp only [hA, hB, Option.map_none]
    | some T =>
        have hB : B.func F (e.toFun ∘ xs) =
            some (Structure.imageSet e.toFun T) := by
          simpa only [hA, Option.map_some] using (e.map_func F xs).symm
        simp only [hA, hB, Option.map_some, Option.some.injEq]
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxy⟩
          refine ⟨x, hx, ?_⟩
          apply Subtype.ext
          exact hxy

/-- The exact range factor has the original vertex map. -/
@[simp] theorem Embedding.codRestrictClosedRange_apply
    {A : PartialSetStructure L U} {B : PartialSetStructure L V}
    (e : Embedding A B) (x : U) :
    (e.codRestrictClosedRange x).1 = e.toFun x := rfl


/-- On a GENUINELY function-closed carrier, whole-fibre weak
induction is literally the genuine full induced Option(Set)
structure. This is an equality of independent domain bits
and entire set-valued fibres, including some empty. -/
theorem wholeWeakInduce_eq_induceClosed_of_isClosed
    (A : PartialSetStructure L V) (S : Set V)
    (hS : A.IsClosed S) :
    A.wholeWeakInduce S = A.induceClosed S hS := by
  classical
  change
    PartialSetStructure.mk
      (fun R xs => A.rel R (Subtype.val ∘ xs))
      (fun F xs => wholeWeakValue S (A.func F (Subtype.val ∘ xs))) =
    PartialSetStructure.mk
      (fun R xs => A.rel R (Subtype.val ∘ xs))
      (fun F xs => (A.func F (Subtype.val ∘ xs)).map
        (fun T => {y : S | y.1 ∈ T}))
  congr 1
  funext F xs
  cases hv : A.func F (Subtype.val ∘ xs) with
  | none =>
      simp only [hv, wholeWeakValue_none, Option.map_none]
  | some T =>
      have hT : T ⊆ S :=
        hS F (Subtype.val ∘ xs) T
          (fun i => (xs i).2) hv
      simpa only [hv, Option.map_some] using
        wholeWeakValue_of_subset S T hT

/-- The same EXACT full-image factorization can target the
whole-fibre weak induced test on that image, because its
carrier is already genuinely function-closed. No generated
hull or premature domain deletion is involved. -/
noncomputable def Embedding.codRestrictWholeWeakRange
    {A : PartialSetStructure L U} {B : PartialSetStructure L V}
    (e : Embedding A B) :
    Embedding A (B.wholeWeakInduce (Set.range e.toFun)) := by
  classical
  have hEq :
      B.wholeWeakInduce (Set.range e.toFun) =
      B.induceClosed (Set.range e.toFun) e.range_isClosed :=
    wholeWeakInduce_eq_induceClosed_of_isClosed
      B (Set.range e.toFun) e.range_isClosed
  rw [hEq]
  exact e.codRestrictClosedRange

end StructuralRamsey.PartialSetStructure
