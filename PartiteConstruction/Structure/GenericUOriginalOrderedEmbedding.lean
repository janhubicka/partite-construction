import PartiteConstruction.Structure.GenericUCombinedClosureBridge
import PartiteConstruction.Structure.GenericUFunctionalOrderedArrowTransfer
import PartiteConstruction.Structure.GenericUOrderedClosureEquiv

/-!
# Exact original named-order / arbitrary reduced-functional embedding contract

A correctly ordered source in the ORIGINAL relational (L,ord,U) language
has precisely the same U-closed induced embeddings into the decoded
arbitrary positive-arity function witness as its reduced mixed-language
encoding has genuine ordered full-function embeddings.

The two existing translations are composed without an extra coherence
condition or an additional vertex. This is the exact source/target
dictionary needed by the printed theorem thm:models2.

Requires the existing separately staged/verified interfaces:
- original named-order deletion + range-closure from #577;
- nonredundant arbitrary-target ordered functional dictionary from #580;
- literal range-closed iff fibre-lift from #581 plus combined identity.
-/

namespace StructuralRamsey
universe u v w
namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- Exact same-carrier embedding equivalence from original named-order
U-closed induced copies to ordered full function embeddings of an
arbitrary nonredundant reduced-language witness. -/
def originalUClosedEmbeddingEquivIntoTarget
    (ord : L.Symbol) (hord : L.arity ord = 2)
    (U : Set L.Symbol) (hordU : ord ∉ U)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (A : RelStructure L V)
    [LinearOrder V] [LinearOrder W]
    (hA : A.NamedOrderCorrect ord hord)
    (C : Structure
      ((L.dropNamedOrder ord).withUFunctionsReduced
        (L.dropNamedOrderU ord U)) W) :
    {e : Embedding A
      ((Structure.toRelU (L.dropNamedOrderU ord U)
          (fun R hR => hU R.1 hR) C).restoreNamedOrder hord) //
        IsUClosedEmbeddingRange U hU e} ≃
    Structure.Embedding
      (((A.dropNamedOrder ord).asUFunctionsReduced
        (L.dropNamedOrderU ord U)
        (fun R hR => hU R.1 hR)).withLinearOrder)
      C.withLinearOrder := by
  let U0 := L.dropNamedOrderU ord U
  let hU0 : ∀ R, R ∈ U0 → 1 ≤ (L.dropNamedOrder ord).arity R :=
    fun R hR => hU R.1 hR
  let D := Structure.toRelU U0 hU0 C
  let A0 := A.dropNamedOrder ord
  let E0 := uClosedEquivNamedOrderFresh ord hord U hordU hU A D hA
  let EF := uClosedOrderedEmbeddingEquivIntoTarget A0 U0 hU0 C
  exact {
    toFun := fun e => by
      let t := E0 e
      let f := t.1.forgetFreshOrder
      have hRange : IsUClosedEmbeddingRange U0 hU0 f := t.2
      have hLift : IsUClosedEmbedding A0 D U0 hU0 f :=
        (isUClosedEmbedding_iff_range U0 hU0 f).mpr hRange
      exact EF ⟨f, ⟨hLift, t.1.strictMono⟩⟩
    invFun := fun g => by
      let t := EF.symm g
      let f := t.1.withOrderOfStrictMono t.2.2
      have hRange : D.IsUClosedSetOn U0 hU0 (Set.range f.toFun) :=
        (isUClosedEmbedding_iff_range U0 hU0 t.1).mp t.2.1
      exact E0.symm ⟨f, hRange⟩
    left_inv := by
      intro e
      apply Subtype.ext
      apply Embedding.ext
      intro x
      rfl
    right_inv := by
      intro g
      apply Structure.Embedding.ext
      intro x
      rfl
  }

end RelStructure
end StructuralRamsey
