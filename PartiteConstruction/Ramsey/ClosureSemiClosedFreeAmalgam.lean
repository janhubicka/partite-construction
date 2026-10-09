import PartiteConstruction.Ramsey.ClosureSemiClosedRange

/-! # Free amalgamation of U-semi-closed structures

The 2019 Picture induction permits intermediate structures in which a
closure relation is only *partially* defined. U-semi-closedness requires
the existing tuples to have valid roots and to be unique over any one
root, not existence of outputs for every root.

When two U-semi-closed structures are freely amalgamated over a
fully U-closed common substructure, the result is still U-semi-closed.
The common closed root supplies any closure tuples that could
otherwise disagree at a shared root. Each side's uniqueness forces
those tuples to be the same.

This theorem does **not** claim the resulting free amalgam is U-closed
(the two sides might both omit outputs at other roots), and does not
enlarge any input vertex set.
-/

namespace StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {H E F C : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Any closure tuple with its root inside the left side must
remain on that side, even if the right side is only U-semi-closed.
The root is U-closed and both structure maps are full embeddings. -/
theorem IsFreeAmalgam.closureTuple_inLeft_of_root_inLeft_semi
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hRight : IsUSemiClosed rules Right)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → C)
    (ht : Whole.rel rule.symbol t)
    (hRootLeft :
      ∀ k : Fin rule.rootSize,
        ∃ a : E, t (k.castLE rule.rootLE) = iL a) :
    ∀ j : Fin (L.arity rule.symbol), ∃ a : E, t j = iL a := by
  classical
  rcases (hFree.rel_iff rule.symbol t).mp ht with
      ⟨a, ha, hEq⟩ | ⟨b, hb, hEq⟩
  · intro j
    exact ⟨a j, congrFun hEq j⟩
  · have hOverlapClosed :
        IsUSubstructure rules Right (Set.range sR) :=
      sR.range_isUSubstructure_of_semiClosed hCommon hRight
    have hRootRange :
        ∀ k : Fin rule.rootSize,
          b (k.castLE rule.rootLE) ∈ Set.range sR := by
      intro k
      obtain ⟨a, ha⟩ := hRootLeft k
      have heq : iL a = iR (b (k.castLE rule.rootLE)) := by
        calc
          iL a = t (k.castLE rule.rootLE) := ha.symm
          _ = iR (b (k.castLE rule.rootLE)) := congrFun hEq _
      obtain ⟨d, _hda, hdb⟩ :=
        (hFree.overlap a (b (k.castLE rule.rootLE))).mp heq
      exact ⟨d, hdb.symm⟩
    have hAllRange :=
      hOverlapClosed rule hrule b hb hRootRange
    intro j
    obtain ⟨d, hd⟩ := hAllRange j
    have hglue : iL (sL d) = iR (sR d) :=
      (hFree.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
    exact ⟨sL d, (congrFun hEq j).trans
      ((congrArg iR hd).symm.trans hglue.symm)⟩

/-- Symmetric closure-tuple range property. -/
theorem IsFreeAmalgam.closureTuple_inRight_of_root_inRight_semi
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → C)
    (ht : Whole.rel rule.symbol t)
    (hRootRight :
      ∀ k : Fin rule.rootSize,
        ∃ b : F, t (k.castLE rule.rootLE) = iR b) :
    ∀ j : Fin (L.arity rule.symbol), ∃ b : F, t j = iR b :=
  hFree.swap.closureTuple_inLeft_of_root_inLeft_semi
    hCommon hLeft rule hrule t ht hRootRight

/-- If a tuple in the amalgam came from the left, it is the
**unique** tuple above its root. A hypothetical right-side tuple
over the same root is first pulled back into the left via the
vertex-exact U-substructure range property of the common root. -/
private theorem IsFreeAmalgam.semiTupleUnique_of_firstLeft
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t₁ t₂ : Fin (L.arity rule.symbol) → C)
    (ht₁ : Whole.rel rule.symbol t₁)
    (ht₂ : Whole.rel rule.symbol t₂)
    (hSameRoot :
      ∀ k : Fin rule.rootSize,
        t₁ (k.castLE rule.rootLE) =
        t₂ (k.castLE rule.rootLE))
    (hFromLeft :
      ∃ a : Fin (L.arity rule.symbol) → E,
        Left.rel rule.symbol a ∧ t₁ = iL ∘ a) :
    t₁ = t₂ := by
  classical
  obtain ⟨a, ha, haEq⟩ := hFromLeft
  rcases (hFree.rel_iff rule.symbol t₂).mp ht₂ with
      ⟨b, hb, hbEq⟩ | ⟨b, hb, hbEq⟩
  · have hRootSide :
        ∀ k : Fin rule.rootSize,
          a (k.castLE rule.rootLE) =
          b (k.castLE rule.rootLE) := by
      intro k
      apply iL.injective
      calc
        iL (a (k.castLE rule.rootLE)) =
            t₁ (k.castLE rule.rootLE) :=
          (congrFun haEq _).symm
        _ = t₂ (k.castLE rule.rootLE) := hSameRoot k
        _ = iL (b (k.castLE rule.rootLE)) :=
          congrFun hbEq _
    have hab : a = b :=
      (hLeft rule hrule).2 a b ha hb hRootSide
    calc
      t₁ = iL ∘ a := haEq
      _ = iL ∘ b := congrArg (fun q => iL ∘ q) hab
      _ = t₂ := hbEq.symm
  · have hRootLeft :
        ∀ k : Fin rule.rootSize,
          ∃ x : E, t₂ (k.castLE rule.rootLE) = iL x := by
      intro k
      refine ⟨a (k.castLE rule.rootLE), ?_⟩
      calc
        t₂ (k.castLE rule.rootLE) =
            t₁ (k.castLE rule.rootLE) :=
          (hSameRoot k).symm
        _ = iL (a (k.castLE rule.rootLE)) :=
          congrFun haEq _
    have hAllLeft :
        ∀ j : Fin (L.arity rule.symbol),
          ∃ x : E, t₂ j = iL x :=
      hFree.closureTuple_inLeft_of_root_inLeft_semi
        hCommon hRight rule hrule t₂ ht₂ hRootLeft
    let bLeft : Fin (L.arity rule.symbol) → E :=
      fun j => Classical.choose (hAllLeft j)
    have hBLeft (j : Fin (L.arity rule.symbol)) :
        t₂ j = iL (bLeft j) :=
      Classical.choose_spec (hAllLeft j)
    have hLeftRel : Left.rel rule.symbol bLeft := by
      apply (iL.map_rel_iff rule.symbol bLeft).mp
      have hbEq : iL ∘ bLeft = t₂ := by
        funext j
        exact (hBLeft j).symm
      rw [hbEq]
      exact ht₂
    have hRootSide :
        ∀ k : Fin rule.rootSize,
          a (k.castLE rule.rootLE) =
          bLeft (k.castLE rule.rootLE) := by
      intro k
      apply iL.injective
      calc
        iL (a (k.castLE rule.rootLE)) =
            t₁ (k.castLE rule.rootLE) :=
          (congrFun haEq _).symm
        _ = t₂ (k.castLE rule.rootLE) := hSameRoot k
        _ = iL (bLeft (k.castLE rule.rootLE)) :=
          hBLeft _
    have hab : a = bLeft :=
      (hLeft rule hrule).2 a bLeft ha hLeftRel hRootSide
    funext j
    calc
      t₁ j = iL (a j) := congrFun haEq j
      _ = iL (bLeft j) :=
        congrArg (fun x => iL (x j)) hab
      _ = t₂ j := (hBLeft j).symm

/-- Free amalgamation of U-semi-closed relational structures over
a fully U-closed common substructure preserves U-semi-closedness.

The result need not be U-closed: root existence is not claimed
outside the shared U-closed source. -/
theorem IsFreeAmalgam.isUSemiClosed
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right) :
    IsUSemiClosed rules Whole := by
  intro rule hrule
  constructor
  · intro t ht
    rcases (hFree.rel_iff rule.symbol t).mp ht with
        ⟨a, ha, haEq⟩ | ⟨b, hb, hbEq⟩
    · obtain ⟨e, he⟩ := (hLeft rule hrule).1 a ha
      refine ⟨iL.comp e, ?_⟩
      intro k
      rw [haEq]
      exact congrArg iL (he k)
    · obtain ⟨e, he⟩ := (hRight rule hrule).1 b hb
      refine ⟨iR.comp e, ?_⟩
      intro k
      rw [hbEq]
      exact congrArg iR (he k)
  · intro t₁ t₂ ht₁ ht₂ hSameRoot
    rcases (hFree.rel_iff rule.symbol t₁).mp ht₁ with
        hFromLeft | hFromRight
    · exact hFree.semiTupleUnique_of_firstLeft
        hCommon hLeft hRight rule hrule
        t₁ t₂ ht₁ ht₂ hSameRoot hFromLeft
    · exact hFree.swap.semiTupleUnique_of_firstLeft
        hCommon hRight hLeft rule hrule
        t₁ t₂ ht₁ ht₂ hSameRoot hFromRight

end StructuralRamsey.RelStructure
