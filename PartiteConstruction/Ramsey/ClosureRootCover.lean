import PartiteConstruction.Ramsey.ClosureDescription2019

/-! # Closed root covers

A relational structure is U-closed when its closure tuples and prescribed
root embeddings are covered by U-closed embedded pieces whose ranges are
relative U-substructures. This criterion proves closedness, rather than
assuming it in order to show that the embedded pieces have closed ranges.

Uniqueness is localised using relative range closedness: any competing
tuple over the given root must stay in the selected piece. No finiteness,
global injectivity of a projection, or free-amalgamation property of a
target class is involved.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}

/-- A closed root cover supplies the complete U-closedness condition.
The tuple-cover hypothesis is needed only for closure relation symbols. -/
theorem isUClosed_of_closed_root_cover
    {V : Type v} {I : Type w} {Carrier : I → Type v}
    (rules : ClosureDescription L) (Whole : RelStructure L V)
    (Piece : ∀ i, RelStructure L (Carrier i))
    (inc : ∀ i, Embedding (Piece i) Whole)
    (hClosed : ∀ i, IsUClosed rules (Piece i))
    (hRange : ∀ i, IsUSubstructure rules Whole (Set.range (inc i)))
    (hTuples : ∀ rule ∈ rules,
      ∀ t : Fin (L.arity rule.symbol) → V, Whole.rel rule.symbol t →
        ∃ i, ∃ x : Fin (L.arity rule.symbol) → Carrier i,
          (Piece i).rel rule.symbol x ∧ t = inc i ∘ x)
    (hRoots : ∀ rule ∈ rules, ∀ e : Embedding rule.root Whole,
      ∃ i, ∃ r : Embedding rule.root (Piece i), ∀ k, inc i (r k) = e k) :
    IsUClosed rules Whole := by
  classical
  intro rule hrule
  constructor
  · intro t ht
    obtain ⟨i, x, hx, htx⟩ := hTuples rule hrule t ht
    obtain ⟨r, hr⟩ := (hClosed i rule hrule).1 x hx
    refine ⟨(inc i).comp r, ?_⟩
    intro k
    calc
      t (k.castLE rule.rootLE) = inc i (x (k.castLE rule.rootLE)) :=
        congrFun htx _
      _ = inc i (r k) := congrArg (inc i) (hr k)
  · intro e
    obtain ⟨i, r, hr⟩ := hRoots rule hrule e
    obtain ⟨x, hx, hUnique⟩ := (hClosed i rule hrule).2 r
    refine ⟨inc i ∘ x, ⟨?_, ?_⟩, ?_⟩
    · exact ((inc i).map_rel_iff rule.symbol x).mpr hx.1
    · intro k
      exact (congrArg (inc i) (hx.2 k)).trans (hr k)
    · intro t ht
      have hInput : ∀ k : Fin rule.rootSize,
          t (k.castLE rule.rootLE) ∈ Set.range (inc i) := by
        intro k
        exact ⟨r k, (hr k).trans (ht.2 k).symm⟩
      have hAll : ∀ k : Fin (L.arity rule.symbol),
          t k ∈ Set.range (inc i) :=
        hRange i rule hrule t ht.1 hInput
      let y : Fin (L.arity rule.symbol) → Carrier i :=
        fun k => Classical.choose (hAll k)
      have hy (k : Fin (L.arity rule.symbol)) : inc i (y k) = t k :=
        Classical.choose_spec (hAll k)
      have hyEq : inc i ∘ y = t := funext hy
      have hyRel : (Piece i).rel rule.symbol y := by
        apply ((inc i).map_rel_iff rule.symbol y).mp
        rw [hyEq]
        exact ht.1
      have hyRoot : ∀ k : Fin rule.rootSize,
          y (k.castLE rule.rootLE) = r k := by
        intro k
        apply (inc i).injective
        exact (hy _).trans ((ht.2 k).trans (hr k).symm)
      have hyx : y = x := hUnique y ⟨hyRel, hyRoot⟩
      exact hyEq.symm.trans (congrArg (fun z => inc i ∘ z) hyx)

end StructuralRamsey.RelStructure
