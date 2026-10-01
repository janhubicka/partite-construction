import PartiteConstruction.Ramsey.FromProjections
import PartiteConstruction.Relational.Order

/-! # Ordered structural Ramsey theorem from a Ramsey family of placements

This is the structural conclusion of the non-induced construction. Its sole
combinatorial input is stated explicitly as `ProjectionRamsey`; proving finite
subset Ramsey and translating increasing subsets into this interface is a
separate obligation.
-/
namespace StructuralRamsey.Partite

universe u v
variable {L : RelLanguage.{u}} {U V P I : Type v}

theorem orderedRamseyFromProjections (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [LinearOrder P]
    [Finite U] [Finite V] [Finite P] [Finite I]
    (β : I → V ↪ P) (hβ : ∀ i, StrictMono (β i))
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : ProjectionRamsey A.ordered B.ordered β κ) :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : RelStructure L W),
      StructuralRamsey.Arrow A.ordered B.ordered (@RelStructure.ordered L W C o.toLT) κ := by
  let Q : (R : L.withOrder.Symbol) → (Fin (L.withOrder.arity R) → P) → Prop := by
    intro R
    cases R with
    | inl _ => exact fun _ => True
    | inr _ => exact fun (x : Fin 2 → P) => x 0 < x 1
  have hQ : ∀ i R x, B.ordered.rel R x → Q R (β i ∘ x) := by
    intro i R x hx
    cases R with
    | inl _ => trivial
    | inr _ => exact hβ i hx
  obtain ⟨W, hW, C, hCQ, hC⟩ := ramseyFromProjections A.ordered B.ordered β κ hRamsey Q hQ
  obtain ⟨o, ho⟩ := RelStructure.exists_order_extension C.toRelStructure C.part
    (fun x y hxy => hCQ (.inr ()) ![x, y] hxy)
  let := o
  exact ⟨W, hW, o, C.toRelStructure.orderReduct,
    RelStructure.arrow_completeOrder A B C.toRelStructure ho κ hC⟩

end StructuralRamsey.Partite
