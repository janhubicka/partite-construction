import PartiteConstruction.Structure.GenericUOrderClosure
import PartiteConstruction.Structure.Relationalize

/-!
# Track F: range-set U-closure is the same as source-fibre lifting

The survey's original U-closed embedding is defined by closure of the
image under every last output coordinate of a designated relation.
The generic function encoding uses an equivalent lifting property:
each target output over the embedded source root is the image of an
actual source output.

This module proves the exact equivalence for INDUCED relational
embeddings, on the same vertex maps, without assuming any particular
shape of the relations, arity beyond 1, irreducibility, or any coherence
condition on a target. It deliberately uses only merged infrastructure,
not the still-draft generic function-language encoding.

Once the latter is verified, its RelLanguage.appendU and
RelStructure.IsUClosedEmbedding are definitional translations of
appendClosureTuple and IsUClosedEmbeddingLift below, respectively.
-/

namespace StructuralRamsey

universe u v w

namespace RelLanguage

/-- The literal last-coordinate graph tuple, with a cast from
arity(R)-1+1 to arity(R). -/
def appendClosureTuple
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (x : Fin (L.arity R - 1) → V) (y : V) :
    Fin (L.arity R) → V :=
  fun i => Structure.funcTuple x y
    (Fin.cast ((Nat.sub_add_cancel hR).symm) i)

/-- The root of an original relation tuple. -/
def closureRoot
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (t : Fin (L.arity R) → V) :
    Fin (L.arity R - 1) → V :=
  fun i => t (Fin.cast (Nat.sub_add_cancel hR) i.castSucc)

/-- The final output coordinate of an original relation tuple. -/
def closureLast
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (t : Fin (L.arity R) → V) : V :=
  t (Fin.cast (Nat.sub_add_cancel hR) (Fin.last (L.arity R - 1)))

@[simp] theorem closureRoot_append
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (x : Fin (L.arity R - 1) → V) (y : V) :
    closureRoot L R hR (appendClosureTuple L R hR x y) = x := by
  funext i
  have h := Nat.sub_add_cancel hR
  change Structure.funcTuple x y
    (Fin.cast h.symm (Fin.cast h i.castSucc)) = x i
  have hc : Fin.cast h.symm (Fin.cast h i.castSucc) = i.castSucc :=
    Fin.ext rfl
  rw [hc]
  exact Structure.funcTuple_castSucc x y i

@[simp] theorem closureLast_append
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (x : Fin (L.arity R - 1) → V) (y : V) :
    closureLast L R hR (appendClosureTuple L R hR x y) = y := by
  have h := Nat.sub_add_cancel hR
  change Structure.funcTuple x y
    (Fin.cast h.symm (Fin.cast h (Fin.last (L.arity R - 1)))) = y
  have hc : Fin.cast h.symm
    (Fin.cast h (Fin.last (L.arity R - 1))) =
      Fin.last (L.arity R - 1) := Fin.ext rfl
  rw [hc]
  exact Structure.funcTuple_last x y

@[simp] theorem appendClosureTuple_root_last
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} (t : Fin (L.arity R) → V) :
    appendClosureTuple L R hR
      (closureRoot L R hR t) (closureLast L R hR t) = t := by
  funext i
  have h := Nat.sub_add_cancel hR
  let q : Fin (L.arity R - 1 + 1) → V :=
    fun j => t (Fin.cast h j)
  change Structure.funcTuple (fun j => q j.castSucc)
    (q (Fin.last (L.arity R - 1))) (Fin.cast h.symm i) = t i
  rw [Structure.funcTuple_eta q]
  have hc : Fin.cast h (Fin.cast h.symm i) = i := Fin.ext rfl
  exact congrArg t hc

@[simp] theorem appendClosureTuple_comp
    (L : RelLanguage.{u}) (R : L.Symbol) (hR : 1 ≤ L.arity R)
    {V : Type v} {W : Type w} (f : V → W)
    (x : Fin (L.arity R - 1) → V) (y : V) :
    f ∘ appendClosureTuple L R hR x y =
      appendClosureTuple L R hR (f ∘ x) (f y) := by
  funext i
  change f (Structure.funcTuple x y
    (Fin.cast ((Nat.sub_add_cancel hR).symm) i)) =
      Structure.funcTuple (f ∘ x) (f y)
        (Fin.cast ((Nat.sub_add_cancel hR).symm) i)
  exact congrFun (Structure.comp_funcTuple f x y) _

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Source-fibre lifting for an induced map: every output over an image
root comes from an output in A. This is the un-reindexed original-L
version of the full-functional closure condition. -/
def IsUClosedEmbeddingLift
    (A : RelStructure L V) (B : RelStructure L W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B) : Prop :=
  ∀ (F : U) (x : Fin (L.arity F.1 - 1) → V) (y : W),
    B.rel F.1 (L.appendClosureTuple F.1 (hU F.1 F.2)
      (e.toFun ∘ x) y) →
    ∃ z, A.rel F.1 (L.appendClosureTuple F.1
      (hU F.1 F.2) x z) ∧ e z = y

/-- The exact original-law dictionary: closure of the actual range is
equivalent to lifting all relation-value fibres, provided e is an
INDUCED embedding (reflection of relations is essential). -/
theorem isUClosedEmbeddingRange_iff_lift
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    IsUClosedEmbeddingRange U hU e ↔
      IsUClosedEmbeddingLift A B U hU e := by
  classical
  constructor
  · intro h F x y hy
    let t : Fin (L.arity F.1) → W :=
      L.appendClosureTuple F.1 (hU F.1 F.2) (e.toFun ∘ x) y
    have hroots : ∀ i : Fin (L.arity F.1 - 1),
        t (Fin.cast (Nat.sub_add_cancel (hU F.1 F.2)) i.castSucc) ∈
          Set.range e.toFun := by
      intro i
      have hr := L.closureRoot_append F.1 (hU F.1 F.2)
        (e.toFun ∘ x) y
      change (L.closureRoot F.1 (hU F.1 F.2) t) i ∈ Set.range e.toFun
      rw [hr]
      exact ⟨x i, rfl⟩
    have hlast := h F.1 F.2 t hy hroots
    have hout : y ∈ Set.range e.toFun := by
      change L.closureLast F.1 (hU F.1 F.2) t ∈
        Set.range e.toFun at hlast
      rw [L.closureLast_append] at hlast
      exact hlast
    rcases hout with ⟨z, hz⟩
    refine ⟨z, ?_, hz⟩
    have hcomp := L.appendClosureTuple_comp F.1 (hU F.1 F.2)
      e.toFun x z
    have hrel : B.rel F.1
        (e.toFun ∘ L.appendClosureTuple F.1 (hU F.1 F.2) x z) := by
      rw [hcomp, hz]
      exact hy
    exact (e.map_rel_iff F.1
      (L.appendClosureTuple F.1 (hU F.1 F.2) x z)).mp hrel
  · intro hlift R hR t hrel hroots
    have hroots' :
        ∀ i : Fin (L.arity R - 1),
          ∃ a : V, e a = (L.closureRoot R (hU R hR) t) i := by
      intro i
      exact hroots i
    choose x hx using hroots'
    have hmap : e.toFun ∘ x = L.closureRoot R (hU R hR) t := by
      funext i
      exact hx i
    have htuple : L.appendClosureTuple R (hU R hR)
        (e.toFun ∘ x) (L.closureLast R (hU R hR) t) = t := by
      rw [hmap]
      exact L.appendClosureTuple_root_last R (hU R hR) t
    have hrel' : B.rel R (L.appendClosureTuple R (hU R hR)
        (e.toFun ∘ x) (L.closureLast R (hU R hR) t)) := by
      rw [htuple]
      exact hrel
    obtain ⟨z, _hz, hez⟩ :=
      hlift ⟨R, hR⟩ x (L.closureLast R (hU R hR) t) hrel'
    exact ⟨z, hez⟩

end RelStructure
end StructuralRamsey
