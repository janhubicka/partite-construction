import PartiteConstruction.Structure.GenericUOrderedReduct

/-!
# Reconstructing the named order from an external linear order

This module packages the exact *same-carrier* order-symbol equivalence needed
after reducing arbitrary (L,U) to positive-arity set-valued functions.
In the resulting arbitrary target, the old order relation is NOT retained.
Its interpretation is reconstructed exclusively from the external order.

No local irreducibility, B-closedness or witness coherence is assumed.
These source-level declarations need exact-head CI before certification.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {ord : L.Symbol}
variable {V : Type v} {W : Type w}

/-- Restore a distinguished named order, reading it ONLY from the target's
external order; all other relations are taken directly from the reduct. -/
def restoreNamedOrder (D : RelStructure (L.dropNamedOrder ord) V)
    (hord : L.arity ord = 2) [LT V] : RelStructure L V where
  rel R t := by
    classical
    by_cases hR : R = ord
    · subst R
      exact t (Fin.cast hord.symm (0 : Fin 2)) <
        t (Fin.cast hord.symm (1 : Fin 2))
    · exact D.rel ⟨R, hR⟩ t

/-- Literal restoration contract at the named-order symbol. -/
@[simp] theorem restoreNamedOrder_rel_order
    (D : RelStructure (L.dropNamedOrder ord) V)
    (hord : L.arity ord = 2) [LT V]
    (t : Fin (L.arity ord) → V) :
    (D.restoreNamedOrder hord).rel ord t ↔
      t (Fin.cast hord.symm (0 : Fin 2)) <
      t (Fin.cast hord.symm (1 : Fin 2)) := by
  classical
  simp [restoreNamedOrder]

/-- Every other relation is untouched, including nullary symbols. -/
@[simp] theorem restoreNamedOrder_rel_ne
    (D : RelStructure (L.dropNamedOrder ord) V)
    (hord : L.arity ord = 2) [LT V]
    (R : L.Symbol) (hR : R ≠ ord) (t : Fin (L.arity R) → V) :
    (D.restoreNamedOrder hord).rel R t ↔ D.rel ⟨R, hR⟩ t := by
  classical
  simp [restoreNamedOrder, hR]

/-- Restore then forget the named order: every non-order relation agrees
literally on the same carrier, without any target coherence condition. -/
theorem drop_restoreNamedOrder_rel_iff
    (D : RelStructure (L.dropNamedOrder ord) V)
    (hord : L.arity ord = 2) [LT V]
    (R : (L.dropNamedOrder ord).Symbol)
    (t : Fin ((L.dropNamedOrder ord).arity R) → V) :
    ((D.restoreNamedOrder hord).dropNamedOrder ord).rel R t ↔
      D.rel R t := by
  exact D.restoreNamedOrder_rel_ne hord R.1 R.2 t

/-- If the original named order equals the strict carrier order, decoding
after forgetting the order reproduces every original relation. -/
theorem restore_dropNamedOrder_rel_iff
    (A : RelStructure L V) (ord : L.Symbol)
    (hord : L.arity ord = 2) [LinearOrder V]
    (hA : A.NamedOrderCorrect ord hord)
    (R : L.Symbol) (t : Fin (L.arity R) → V) :
    ((A.dropNamedOrder ord).restoreNamedOrder hord).rel R t ↔
      A.rel R t := by
  classical
  by_cases hR : R = ord
  · subst R
    exact (restoreNamedOrder_rel_order (A.dropNamedOrder ord) hord t).trans
      (hA t).symm
  · exact (restoreNamedOrder_rel_ne (A.dropNamedOrder ord) hord R hR t).trans
      Iff.rfl

namespace Embedding

variable {A : RelStructure L V}
variable {D : RelStructure (L.dropNamedOrder ord) W}

/-- Recover a strictly monotone map from an induced embedding into an actual
order-restored target.  The source must interpret its named order correctly. -/
theorem strictMono_of_restored
    (hord : L.arity ord = 2)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord)
    (e : Embedding A (D.restoreNamedOrder hord)) :
    StrictMono e := by
  intro x y hxy
  let t : Fin (L.arity ord) → V :=
    fun i => (![x, y] : Fin 2 → V) (Fin.cast hord i)
  have h0 : t (Fin.cast hord.symm (0 : Fin 2)) = x := by
    change (![x, y] : Fin 2 → V)
      (Fin.cast hord (Fin.cast hord.symm (0 : Fin 2))) = x
    have hcast : Fin.cast hord (Fin.cast hord.symm (0 : Fin 2)) = 0 :=
      Fin.ext rfl
    rw [hcast]
    rfl
  have h1 : t (Fin.cast hord.symm (1 : Fin 2)) = y := by
    change (![x, y] : Fin 2 → V)
      (Fin.cast hord (Fin.cast hord.symm (1 : Fin 2))) = y
    have hcast : Fin.cast hord (Fin.cast hord.symm (1 : Fin 2)) = 1 :=
      Fin.ext rfl
    rw [hcast]
    rfl
  have hsrc : A.rel ord t := (hA t).mpr (by simpa only [h0, h1] using hxy)
  have htgt : (D.restoreNamedOrder hord).rel ord (e.toFun ∘ t) :=
    (e.map_rel_iff ord t).mpr hsrc
  have htgt_lt := (restoreNamedOrder_rel_order D hord (e.toFun ∘ t)).mp htgt
  simpa only [Function.comp_apply, h0, h1] using htgt_lt

/-- Forget the named order from an embedding into an arbitrary restored
target. The target's remaining relations need no coherence assumption. -/
def toDroppedRestored
    (hord : L.arity ord = 2) [LT W]
    (e : Embedding A (D.restoreNamedOrder hord)) :
    Embedding (A.dropNamedOrder ord) D where
  toFun := e
  injective := e.injective
  map_rel_iff R t :=
    (restoreNamedOrder_rel_ne D hord R.1 R.2 (e.toFun ∘ t)).symm.trans
      (e.map_rel_iff R.1 t)

/-- Inverse construction: a reduced embedding which is strictly monotone
is an induced embedding of all original symbols, including named order. -/
def ofDroppedRestored
    (hord : L.arity ord = 2)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord)
    (f : Embedding (A.dropNamedOrder ord) D)
    (hf : StrictMono f) :
    Embedding A (D.restoreNamedOrder hord) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R t
    by_cases hR : R = ord
    · subst R
      calc
        (D.restoreNamedOrder hord).rel ord (f.toFun ∘ t) ↔
          f (t (Fin.cast hord.symm (0 : Fin 2))) <
            f (t (Fin.cast hord.symm (1 : Fin 2))) := by
              simpa only [Function.comp_apply] using
                restoreNamedOrder_rel_order D hord (f.toFun ∘ t)
        _ ↔ t (Fin.cast hord.symm (0 : Fin 2)) <
              t (Fin.cast hord.symm (1 : Fin 2)) := hf.lt_iff_lt
        _ ↔ A.rel ord t := (hA t).symm
    · exact (restoreNamedOrder_rel_ne D hord R hR (f.toFun ∘ t)).trans
        (f.map_rel_iff ⟨R, hR⟩ t)

/-- Full equivalence of genuine named-order embeddings and order-preserving
embeddings of the order-free reduct, without losing any relation symbols. -/
def equivDroppedRestored
    (hord : L.arity ord = 2)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord) :
    Embedding A (D.restoreNamedOrder hord) ≃
      {f : Embedding (A.dropNamedOrder ord) D // StrictMono f} where
  toFun e :=
    ⟨e.toDroppedRestored hord, strictMono_of_restored hord hA e⟩
  invFun f := ofDroppedRestored hord hA f.1 f.2
  left_inv := by
    intro e
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl

end Embedding
end RelStructure
end StructuralRamsey
