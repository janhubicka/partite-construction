import PartiteConstruction.Ramsey.Finite
import PartiteConstruction.Ramsey.FromProjections
import PartiteConstruction.Relational.Order

/-! # Ordered structural Ramsey theorem from a Ramsey family of placements

The structural construction is first exposed with an explicit
`ProjectionRamsey` input. The finite Ramsey theorem for increasing tuples then
supplies that input and yields the unconditional ordered non-induced theorem.
-/
namespace StructuralRamsey.Partite

universe u v w
variable {L : RelLanguage.{u}} {U V I : Type v} {P : Type w}

def IncreasingInjection (V : Type v) (P : Type w) [Preorder V] [Preorder P] :=
  {f : V ↪ P // StrictMono f}

instance [Preorder V] [Preorder P] [Finite V] [Finite P] :
    Finite (IncreasingInjection V P) := by
  apply Finite.of_injective (fun f : IncreasingInjection V P => (f.1 : V → P))
  intro f g h
  apply Subtype.ext
  ext x
  exact congrFun h x

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


/-- Ordinary finite Ramsey supplies a finite ordered family of increasing
placements satisfying the abstract projection-Ramsey input. -/
theorem increasingProjectionRamsey (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ N : ℕ, ProjectionRamsey A.ordered B.ordered
      (fun i : IncreasingInjection V (Fin N) => i.1) κ := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨N, hN⟩ :=
    FiniteRamsey.strictMono κ (Fintype.card U) (Fintype.card V)
  refine ⟨N, ?_⟩
  intro θ
  let uIso : Fin (Fintype.card U) ≃o (Finset.univ : Finset U) :=
    (Finset.univ : Finset U).orderIsoOfFin (by simp)
  let uRank : U → Fin (Fintype.card U) :=
    fun x => uIso.symm ⟨x, Finset.mem_univ x⟩
  have huRank : StrictMono uRank := by
    intro x y hxy
    exact uIso.symm.strictMono hxy
  let toProjection : ∀ a : Fin (Fintype.card U) → Fin N, StrictMono a → U ↪ Fin N :=
    fun a ha => ⟨fun x => a (uRank x), ha.injective.comp huRank.injective⟩
  let colour : (Fin (Fintype.card U) → Fin N) → κ := fun a =>
    if ha : StrictMono a then θ (toProjection a ha)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨S, hScard, hS⟩ := hN colour
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := S) hScard
  let vIso : Fin (Fintype.card V) ≃o (Finset.univ : Finset V) :=
    (Finset.univ : Finset V).orderIsoOfFin (by simp)
  let vRank : V → Fin (Fintype.card V) :=
    fun x => vIso.symm ⟨x, Finset.mem_univ x⟩
  have hvRank : StrictMono vRank := by
    intro x y hxy
    exact vIso.symm.strictMono hxy
  let βfun : V → Fin N := fun x => T.orderEmbOfFin hTcard (vRank x)
  have hβfun : StrictMono βfun :=
    (T.orderEmbOfFin hTcard).strictMono.comp hvRank
  let βemb : V ↪ Fin N := ⟨βfun, hβfun.injective⟩
  let i : IncreasingInjection V (Fin N) := ⟨βemb, hβfun⟩
  refine ⟨i, ?_⟩
  intro e₁ e₂
  let tuple (e : RelStructure.Embedding A.ordered B.ordered) :
      Fin (Fintype.card U) → Fin N :=
    fun j => βemb (e (uIso j).val)
  have htuple (e : RelStructure.Embedding A.ordered B.ordered) :
      StrictMono (tuple e) := by
    intro x y hxy
    apply hβfun
    apply e.strictMono
    exact uIso.strictMono hxy
  have hmem (e : RelStructure.Embedding A.ordered B.ordered) :
      ∀ j, tuple e j ∈ S := by
    intro j
    apply hTsub
    simpa [tuple, βemb, βfun] using
      T.orderEmbOfFin_mem hTcard (vRank (e (uIso j).val))
  have hprojection (e : RelStructure.Embedding A.ordered B.ordered) :
      toProjection (tuple e) (htuple e) =
        copyProjection A.ordered B.ordered
          (fun j : IncreasingInjection V (Fin N) => j.1) i e := by
    apply Function.Embedding.ext
    intro x
    change βemb (e (uIso (uRank x)).val) = βemb (e x)
    have hx := uIso.apply_symm_apply ⟨x, Finset.mem_univ x⟩
    exact congrArg (fun y => βemb (e y.val)) hx
  have hcolour (e : RelStructure.Embedding A.ordered B.ordered) :
      colour (tuple e) =
        θ (copyProjection A.ordered B.ordered
          (fun j : IncreasingInjection V (Fin N) => j.1) i e) := by
    simp only [colour, dif_pos (htuple e)]
    rw [hprojection e]
  have h := hS (tuple e₁) (tuple e₂) (htuple e₁) (htuple e₂) (hmem e₁) (hmem e₂)
  rw [hcolour e₁, hcolour e₂] at h
  exact h

/-- Unconditional finite ordered structural Ramsey theorem obtained by the
non-induced partite construction. -/
theorem orderedRamsey (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (C : RelStructure L W),
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ := by
  classical
  obtain ⟨N, hRamsey⟩ := increasingProjectionRamsey A B κ
  let β : IncreasingInjection V (Fin N) → V ↪ Fin N := fun i => i.1
  have hβ : ∀ i, StrictMono (β i) := fun i => i.2
  exact orderedRamseyFromProjections A B β hβ κ hRamsey

end StructuralRamsey.Partite
