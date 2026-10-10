import PartiteConstruction.Ramsey.ClosureTaggedParts

/-! # Root-tagged part predicates preserve U-closedness

The exact tagged expansion of the preceding module uses a distinct
closure-relation symbol for each root part profile. This file transports
full relational embeddings, root embeddings and the existence/uniqueness
clauses of U-closedness. Every old relation is retained. Thus a labelled
tuple matches exactly its own tagged rule, avoiding the false shared-symbol
multi-root interpretation.

No claim is made here about free decompositions, intrinsic U-irreducibility,
relative completion maps, Ramsey classes or the full recursive construction.
-/

namespace StructuralRamsey.RelStructure

universe u v w z
variable {L : RelLanguage.{u}} {P : Type v}
variable {V : Type w} {W : Type z}

/-- Full induced embeddings preserving part labels lift to the tagged
language. The tagged relation cases require both old relation reflection
and equality of every designated root label. -/
def Embedding.expandTaggedClosureParts
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) (partA : V → P) (partB : W → P)
    (hPart : ∀ x, partB (e x) = partA x) :
    Embedding (RelStructure.expandTaggedClosureParts rules A partA)
      (RelStructure.expandTaggedClosureParts rules B partB) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R => exact e.map_rel_iff R xs
    | inr R =>
      cases R with
      | inl tag =>
        constructor
        · intro ht
          constructor
          · exact (e.map_rel_iff tag.rule.symbol xs).mp ht.1
          · intro i
            have h := ht.2 i
            simpa only [Function.comp_apply, hPart] using h
        · intro ht
          constructor
          · exact (e.map_rel_iff tag.rule.symbol xs).mpr ht.1
          · intro i
            exact (hPart (xs (i.castLE tag.rule.rootLE))).trans (ht.2 i)
      | inr p =>
        change (partB (e (xs (RelLanguage.taggedParts_partIndex L rules P p))) = p) ↔
          (partA (xs (RelLanguage.taggedParts_partIndex L rules P p)) = p)
        rw [hPart]

/-- Forget tagged and unary part relations, retaining all original
positive AND negative relation information. -/
def Embedding.forgetTaggedClosureParts
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (RelStructure.expandTaggedClosureParts rules A partA)
      (RelStructure.expandTaggedClosureParts rules B partB)) :
    Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs

/-- Every tagged-language embedding respects its unary part labels. -/
theorem Embedding.tagged_preserves_part
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {partA : V → P} {partB : W → P}
    (e : Embedding (RelStructure.expandTaggedClosureParts rules A partA)
      (RelStructure.expandTaggedClosureParts rules B partB)) (x : V) :
    partB (e x) = partA x := by
  have h := (e.map_rel_iff (.inr (.inr (partA x)))
    (fun _ : Fin 1 => x)).mpr
    (show (RelStructure.expandTaggedClosureParts rules A partA).rel
      (.inr (.inr (partA x))) (fun _ : Fin 1 => x) from rfl)
  exact h

/-- Original U-closedness is EQUIVALENT to U-closedness under the
proper root-tagged expansion. Note that the target uses the root-tagged
description, not the invalid simple named-parts root lift. -/
theorem isUClosed_iff_taggedParts
    (rules : ClosureDescription L)
    (A : RelStructure L V) (part : V → P) :
    IsUClosed rules A ↔
      IsUClosed (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) := by
  constructor
  · intro hA newRule hNew
    obtain ⟨tag, rfl⟩ := hNew
    constructor
    · intro t ht
      obtain ⟨e, he⟩ := (hA tag.rule tag.rule_mem).1 t ht.1
      have hPart : ∀ i, part (e i) = tag.rootParts i := by
        intro i
        rw [← he i]
        exact ht.2 i
      refine ⟨e.expandTaggedClosureParts tag.rootParts part hPart, ?_⟩
      exact he
    · intro eExp
      let e : Embedding tag.rule.root A :=
        eExp.forgetTaggedClosureParts
      have hPart : ∀ i, part (e i) = tag.rootParts i :=
        eExp.tagged_preserves_part
      obtain ⟨t, ht, hUnique⟩ := (hA tag.rule tag.rule_mem).2 e
      refine ⟨t, ⟨⟨ht.1, ?_⟩, ht.2⟩, ?_⟩
      · intro i
        rw [ht.2 i]
        exact hPart i
      · intro s hs
        exact hUnique s ⟨hs.1.1, hs.2⟩
  · intro hExp rule hrule
    constructor
    · intro t ht
      let tag : ClosurePartTag L rules P := {
        rule := rule
        rule_mem := hrule
        rootParts := fun i => part (t (i.castLE rule.rootLE))
      }
      have htTag :
          (RelStructure.expandTaggedClosureParts rules A part).rel tag.liftRule.symbol t :=
        ⟨ht, fun _ => rfl⟩
      obtain ⟨eExp, he⟩ :=
        (hExp tag.liftRule tag.liftRule_mem).1 t htTag
      exact ⟨eExp.forgetTaggedClosureParts, he⟩
    · intro e
      let tag : ClosurePartTag L rules P := {
        rule := rule
        rule_mem := hrule
        rootParts := fun i => part (e i)
      }
      let eExp : Embedding tag.liftRule.root
          (RelStructure.expandTaggedClosureParts rules A part) :=
        e.expandTaggedClosureParts tag.rootParts part (fun _ => rfl)
      obtain ⟨t, ht, hUnique⟩ :=
        (hExp tag.liftRule tag.liftRule_mem).2 eExp
      refine ⟨t, ⟨ht.1.1, ht.2⟩, ?_⟩
      intro s hs
      have hsTag :
          (RelStructure.expandTaggedClosureParts rules A part).rel tag.liftRule.symbol s := by
        refine ⟨hs.1, ?_⟩
        intro i
        rw [hs.2 i]
        rfl
      exact hUnique s ⟨hsTag, hs.2⟩

end StructuralRamsey.RelStructure
