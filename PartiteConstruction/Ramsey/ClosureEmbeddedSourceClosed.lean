import PartiteConstruction.Ramsey.ClosureEmbeddingRange
import PartiteConstruction.Ramsey.ClosureUSubstructurePreimage

/-! # U-closedness transferred to exact embedded relative substructures

In a U-closed ambient structure, an embedded vertex set closed relative
to the ambient structure is itself U-closed.  This is the reverse
embedding transport direction missing from Lemma 2.23(1)'s
same-carrier `induce_iff_USubstructure`.

No hull is generated.  The proof pulls each closure tuple through the
full embedding and uses injectivity plus unique closure tuples in the
ambient target.  The source and target may have different carriers.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Exact U-substructure images in U-closed targets are intrinsically
U-closed on their original source carrier. -/
theorem Embedding.source_isUClosed_of_range_USubstructure
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (e : Embedding A B)
    (hB : IsUClosed rules B)
    (hRange : IsUSubstructure rules B (Set.range e)) :
    IsUClosed rules A := by
  classical
  intro rule hrule
  constructor
  · intro t ht
    have htB : B.rel rule.symbol (e ∘ t) :=
      (e.map_rel_iff rule.symbol t).mpr ht
    obtain ⟨rB, hrB⟩ := (hB rule hrule).1 (e ∘ t) htB
    have hrange : ∀ i : Fin rule.rootSize,
        ∃ a : U, rB i = e a := by
      intro i
      exact ⟨t (i.castLE rule.rootLE), (hrB i).symm⟩
    let rA : Embedding rule.root A :=
      rB.factorThroughRangeHeterogeneous e hrange
    refine ⟨rA, ?_⟩
    intro i
    apply e.injective
    calc
      e (t (i.castLE rule.rootLE)) =
          rB i := hrB i
      _ = e (rA i) := Classical.choose_spec (hrange i)
  · intro rA
    let rB : Embedding rule.root B := e.comp rA
    obtain ⟨tB, htB, hUniqueB⟩ := (hB rule hrule).2 rB
    have hRootRange :
        ∀ i : Fin rule.rootSize,
          tB (i.castLE rule.rootLE) ∈ Set.range e := by
      intro i
      rw [htB.2 i]
      exact ⟨rA i, rfl⟩
    have hWholeRange :
        ∀ j : Fin (L.arity rule.symbol), tB j ∈ Set.range e :=
      hRange rule hrule tB htB.1 hRootRange
    let tA : Fin (L.arity rule.symbol) → U :=
      fun j => Classical.choose (hWholeRange j)
    have htAeq (j : Fin (L.arity rule.symbol)) :
        e (tA j) = tB j :=
      Classical.choose_spec (hWholeRange j)
    have hTupleEq : e ∘ tA = tB := by
      funext j
      exact htAeq j
    have htA : A.rel rule.symbol tA := by
      apply (e.map_rel_iff rule.symbol tA).mp
      rw [hTupleEq]
      exact htB.1
    have hRootA :
        ∀ i : Fin rule.rootSize,
          tA (i.castLE rule.rootLE) = rA i := by
      intro i
      apply e.injective
      calc
        e (tA (i.castLE rule.rootLE)) =
            tB (i.castLE rule.rootLE) := htAeq _
        _ = rB i := htB.2 i
        _ = e (rA i) := rfl
    refine ⟨tA, ⟨htA, hRootA⟩, ?_⟩
    intro q hq
    have hqB : B.rel rule.symbol (e ∘ q) :=
      (e.map_rel_iff rule.symbol q).mpr hq.1
    have hqRoot :
        ∀ i : Fin rule.rootSize,
          (e ∘ q) (i.castLE rule.rootLE) = rB i := by
      intro i
      exact congrArg e (hq.2 i)
    have hqEq : e ∘ q = tB :=
      hUniqueB (e ∘ q) ⟨hqB, hqRoot⟩
    funext j
    apply e.injective
    exact (congrFun hqEq j).trans (htAeq j).symm

end StructuralRamsey.RelStructure
