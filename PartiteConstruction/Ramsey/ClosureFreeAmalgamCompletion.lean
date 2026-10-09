import PartiteConstruction.Ramsey.ClosureFreeAmalgam

/-! # Relational U-closedness under full free amalgamation

This completes the root-existence-and-uniqueness part of
Hubička--Nešetřil (2019), Lemma 2.23(2). If the common root and both
sides are U-closed, their free amalgam is U-closed.

Crucially, the common structure must itself be U-closed: otherwise
both sides can independently extend one closure root and create
different outputs in the free amalgam. No generated closure hull is
taken; all vertex sets are those of the actual free-amalgam diagram.
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

/-- Reversal of an arbitrary full relational free-amalgam diagram. -/
theorem IsFreeAmalgam.swap
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam sR sL iR iL := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rcases hFree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inr ⟨a, ha⟩
    · exact Or.inl ⟨b, hb⟩
  · intro b a
    constructor
    · intro heq
      obtain ⟨d, ha, hb⟩ := (hFree.overlap a b).mp heq.symm
      exact ⟨d, hb, ha⟩
    · rintro ⟨d, hb, ha⟩
      exact ((hFree.overlap a b).mpr ⟨d, ha, hb⟩).symm
  · intro R t
    exact (hFree.rel_iff R t).trans or_comm

/-- Every closure tuple whose root lies in the left side lies
entirely in that side. This is the exact vertex-set version of
closure under free amalgamation, and uses U-closedness of the
common structure, not U-closedness of the whole amalgam. -/
theorem IsFreeAmalgam.closureTuple_inLeft_of_root_inLeft
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hRight : IsUClosed rules Right)
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
      sR.range_isUSubstructure hCommon hRight
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

/-- Symmetric form of the closure tuple range lemma. -/
theorem IsFreeAmalgam.closureTuple_inRight_of_root_inRight
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → C)
    (ht : Whole.rel rule.symbol t)
    (hRootRight :
      ∀ k : Fin rule.rootSize,
        ∃ b : F, t (k.castLE rule.rootLE) = iR b) :
    ∀ j : Fin (L.arity rule.symbol), ∃ b : F, t j = iR b :=
  hFree.swap.closureTuple_inLeft_of_root_inLeft
    hCommon hLeft rule hrule t ht hRootRight

/-- The unique closure tuple above a root embedded into one side
persists in the whole free amalgam. Any other tuple over the
same root must return entirely to that side, and is therefore
equal by side uniqueness. -/
theorem IsFreeAmalgam.closureTuple_existsUnique_left
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root Whole)
    (hRange : ∀ k : Fin rule.rootSize, ∃ a : E, e k = iL a) :
    ∃! t : Fin (L.arity rule.symbol) → C,
      Whole.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize,
        t (k.castLE rule.rootLE) = e k := by
  classical
  let eLeft : Embedding rule.root Left :=
    e.factorThroughRangeHeterogeneous iL hRange
  have heLeft (k : Fin rule.rootSize) :
      e k = iL (eLeft k) :=
    Classical.choose_spec (hRange k)
  obtain ⟨tLeft, hTupleLeft, hUniqueLeft⟩ :=
    (hLeft rule hrule).2 eLeft
  let tWhole : Fin (L.arity rule.symbol) → C :=
    iL ∘ tLeft
  refine ⟨tWhole, ⟨?_, ?_⟩, ?_⟩
  · exact (iL.map_rel_iff rule.symbol tLeft).2 hTupleLeft.1
  · intro k
    exact (congrArg iL (hTupleLeft.2 k)).trans (heLeft k).symm
  · intro t hTuple
    have hRootLeft :
        ∀ k : Fin rule.rootSize,
          ∃ a : E, t (k.castLE rule.rootLE) = iL a := by
      intro k
      exact ⟨eLeft k, (hTuple.2 k).trans (heLeft k)⟩
    have hAllLeft : ∀ j, ∃ a : E, t j = iL a :=
      hFree.closureTuple_inLeft_of_root_inLeft
        hCommon hRight rule hrule t hTuple.1 hRootLeft
    let b : Fin (L.arity rule.symbol) → E :=
      fun j => Classical.choose (hAllLeft j)
    have hb (j : Fin (L.arity rule.symbol)) :
        t j = iL (b j) :=
      Classical.choose_spec (hAllLeft j)
    have hLeftRel : Left.rel rule.symbol b := by
      apply (iL.map_rel_iff rule.symbol b).mp
      have heq : iL ∘ b = t := by
        funext j
        exact (hb j).symm
      rw [heq]
      exact hTuple.1
    have hLeftRoot (k : Fin rule.rootSize) :
        b (k.castLE rule.rootLE) = eLeft k := by
      apply iL.injective
      calc
        iL (b (k.castLE rule.rootLE)) =
            t (k.castLE rule.rootLE) := (hb _).symm
        _ = e k := hTuple.2 k
        _ = iL (eLeft k) := heLeft k
    have heq : b = tLeft :=
      hUniqueLeft b ⟨hLeftRel, hLeftRoot⟩
    funext j
    calc
      t j = iL (b j) := hb j
      _ = iL (tLeft j) := congrArg iL (congrFun heq j)

/-- Symmetric uniqueness over a right-side root. -/
theorem IsFreeAmalgam.closureTuple_existsUnique_right
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root Whole)
    (hRange : ∀ k : Fin rule.rootSize, ∃ b : F, e k = iR b) :
    ∃! t : Fin (L.arity rule.symbol) → C,
      Whole.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize,
        t (k.castLE rule.rootLE) = e k :=
  hFree.swap.closureTuple_existsUnique_left
    hCommon hRight hLeft rule hrule e hRange

/-- All those Ramsey classes (2019), Lemma 2.23(2):
U-closed relational structures are closed under free
amalgamation along a common full U-closed substructure.
The resulting closure is on the *same exact amalgam vertices*. -/
theorem IsFreeAmalgam.isUClosed
    {rules : ClosureDescription L}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hCommon : IsUClosed rules Root)
    (hLeft : IsUClosed rules Left)
    (hRight : IsUClosed rules Right) :
    IsUClosed rules Whole := by
  intro rule hrule
  constructor
  · intro t ht
    exact hFree.closureTuple_hasRoot rule
      (hLeft rule hrule) (hRight rule hrule) t ht
  · intro e
    have hIrred :
        (Whole.induce (Set.range e)).Irreducible :=
      rule.rootIrreducible.range_embedding e
    rcases hFree.irreducible_side (Set.range e) hIrred with
        hInLeft | hInRight
    · have hRange :
          ∀ k : Fin rule.rootSize, ∃ a : E, e k = iL a := by
        intro k
        obtain ⟨a, ha⟩ := hInLeft ⟨e k, ⟨k, rfl⟩⟩
        exact ⟨a, ha⟩
      exact hFree.closureTuple_existsUnique_left
        hCommon hLeft hRight rule hrule e hRange
    · have hRange :
          ∀ k : Fin rule.rootSize, ∃ b : F, e k = iR b := by
        intro k
        obtain ⟨b, hb⟩ := hInRight ⟨e k, ⟨k, rfl⟩⟩
        exact ⟨b, hb⟩
      exact hFree.closureTuple_existsUnique_right
        hCommon hLeft hRight rule hrule e hRange

end StructuralRamsey.RelStructure
