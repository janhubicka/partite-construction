import PartiteConstruction.Structure.GenericUOutputTransversal
import PartiteConstruction.Structure.GenericUOrderClosure

/-!
# Track F: original U-closed subsets are exactly graph-function-closed subsets

The survey's U-closedness asks that the image of every designated relation
last coordinate stay in a subset whenever all root coordinates are there.
The graph-language construction expresses this as FunctionClosedSet.

The two predicates have the same carrier S and the same relation witnesses
under the nonredundant U-function encoding. Neither finite language, U-
transversality, irreducibility nor a closure-hull construction is needed.
-/

namespace StructuralRamsey

universe u v

namespace Partite.System

variable {L : RelLanguage.{u}} {P V : Type v}

/-- The original arbitrary-L last-coordinate U-closedness agrees literally
with closure for the function-graph relations of the translated partite
system, without requiring outputs to be singleton-valued or nonempty. -/
theorem originalUClosedSet_iff_functionClosed
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (S : Set V) :
    B.toRelStructure.IsUClosedSetOn U hU S ↔
      (B.asReducedUGraph U hU).toRelStructure.FunctionClosedSet S := by
  constructor
  · intro h F x y hy hroots
    have htuple : B.rel F.1
        (RelLanguage.appendU L U hU F x y) :=
      (B.reducedUGraph_func_snoc_iff U hU F x y).mp hy
    have hroot :
        ∀ i : Fin (L.arity F.1 - 1),
          (RelLanguage.appendU L U hU F x y)
            (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)) i.castSucc) ∈ S := by
      intro i
      change (RelLanguage.rootU L U hU F
        (RelLanguage.appendU L U hU F x y)) i ∈ S
      rw [RelLanguage.rootU_append]
      exact hroots i
    have hout := h F.1 F.2
      (RelLanguage.appendU L U hU F x y) htuple hroot
    change (RelLanguage.lastU L U hU F
      (RelLanguage.appendU L U hU F x y)) ∈ S at hout
    rw [RelLanguage.lastU_append] at hout
    exact hout
  · intro h R hR t ht hroots
    let F : U := ⟨R, hR⟩
    let x := RelLanguage.rootU L U hU F t
    let y := RelLanguage.lastU L U hU F t
    have ht' : B.rel F.1 (RelLanguage.appendU L U hU F x y) := by
      rw [RelLanguage.appendU_root_last]
      exact ht
    have hgraph :
        (B.asReducedUGraph U hU).rel (.inr F)
          (Structure.funcTuple x y) :=
      (B.reducedUGraph_func_snoc_iff U hU F x y).mpr ht'
    have hroots' : ∀ i : Fin (L.arity F.1 - 1), x i ∈ S := by
      intro i
      exact hroots i
    exact h F x y hgraph hroots'

end Partite.System
end StructuralRamsey
