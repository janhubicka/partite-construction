import PartiteConstruction.Ramsey.ClosurePartPredicates

/-! # Root-tagged part predicates for genuine closure descriptions

A naive expansion which gives different unary-part-labelled roots to the
SAME closure-relation symbol is inconsistent with Definition 2.12: every
tuple bearing that symbol must match EVERY rule associated to the symbol.

Here each root assignment is given its own NEW tagged relation symbol.
The expanded signature retains the original relations and adds unary
part predicates. A tagged closure relation is interpreted as the
corresponding old relation with precisely that root-part assignment.
Each tagged closure rule therefore has its own fixed induced root.

This first module proves that U-substructure (relative closure of an
EXACT vertex set) is equivalent before/after the correct expansion.
It does not yet transport U-closedness, U-irreducibility or Ramsey arrows;
those are independent obligations in the unrestricted initial repair.
-/

namespace StructuralRamsey

universe u v w

namespace RelStructure

/-- A closure-symbol tag includes the original rule and the part labels
of every vertex of its finite prescribed root. -/
structure ClosurePartTag
    (L : RelLanguage.{u}) (rules : ClosureDescription L)
    (P : Type v) where
  rule : ClosureRule L
  rule_mem : rule ∈ rules
  rootParts : Fin rule.rootSize → P

end RelStructure

namespace RelLanguage

/-- Full relational language with original relations, independently
tagged closure relations, and unary predicates naming the parts. -/
def withTaggedClosureParts
    (L : RelLanguage.{u}) (rules : RelStructure.ClosureDescription L)
    (P : Type v) : RelLanguage.{max u v} where
  Symbol := L.Symbol ⊕ (RelStructure.ClosurePartTag L rules P ⊕ P)
  arity
    | .inl R => L.arity R
    | .inr (.inl tag) => L.arity tag.rule.symbol
    | .inr (.inr _) => 1

@[simp] theorem taggedParts_arity_original
    (L : RelLanguage.{u}) (rules : RelStructure.ClosureDescription L)
    (P : Type v) (R : L.Symbol) :
    (L.withTaggedClosureParts rules P).arity (.inl R) = L.arity R := rfl

@[simp] theorem taggedParts_arity_tag
    (L : RelLanguage.{u}) (rules : RelStructure.ClosureDescription L)
    (P : Type v) (tag : RelStructure.ClosurePartTag L rules P) :
    (L.withTaggedClosureParts rules P).arity (.inr (.inl tag)) =
      L.arity tag.rule.symbol := rfl

@[simp] theorem taggedParts_arity_part
    (L : RelLanguage.{u}) (rules : RelStructure.ClosureDescription L)
    (P : Type v) (p : P) :
    (L.withTaggedClosureParts rules P).arity (.inr (.inr p)) = 1 := rfl

/-- Coordinate zero of a tagged-language unary part predicate. -/
def taggedParts_partIndex
    (L : RelLanguage.{u}) (rules : RelStructure.ClosureDescription L)
    (P : Type v) (p : P) :
    Fin ((L.withTaggedClosureParts rules P).arity (.inr (.inr p))) :=
  ⟨0, by simp⟩

end RelLanguage

namespace RelStructure

variable {L : RelLanguage.{u}} {P : Type v} {V : Type w}

/-- Every tagged relation has the original tuple and the advertised root
part profile. Unsuffixed old relation symbols are retained unchanged. -/
def expandTaggedClosureParts (rules : ClosureDescription L)
    (A : RelStructure L V) (part : V → P) :
    RelStructure (L.withTaggedClosureParts rules P) V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr (.inl tag), xs =>
        A.rel tag.rule.symbol xs ∧
          ∀ i : Fin tag.rule.rootSize,
            part (xs (i.castLE tag.rule.rootLE)) = tag.rootParts i
    | .inr (.inr p), xs =>
        part (xs (RelLanguage.taggedParts_partIndex L rules P p)) = p

/-- A separate designated relation symbol for every labelled root. -/
def ClosurePartTag.liftRule
    {rules : ClosureDescription L} (tag : ClosurePartTag L rules P) :
    ClosureRule (L.withTaggedClosureParts rules P) where
  symbol := .inr (.inl tag)
  rootSize := tag.rule.rootSize
  rootPositive := tag.rule.rootPositive
  rootStrict := tag.rule.rootStrict
  root := expandTaggedClosureParts rules tag.rule.root tag.rootParts
  rootIrreducible := by
    intro x y hxy
    obtain ⟨R, xs, i, j, ht, hi, hj⟩ := tag.rule.rootIrreducible hxy
    exact ⟨.inl R, xs, i, j, ht, hi, hj⟩

/-- The genuine lifted closure description: all labelled roots get
different tagged relation symbols, rather than sharing one symbol. -/
def ClosureDescription.withTaggedClosureParts
    (rules : ClosureDescription L) (P : Type v) :
    ClosureDescription (L.withTaggedClosureParts rules P) :=
  {r | ∃ tag : ClosurePartTag L rules P, r = tag.liftRule}

theorem ClosurePartTag.liftRule_mem
    {rules : ClosureDescription L} (tag : ClosurePartTag L rules P) :
    tag.liftRule ∈ rules.withTaggedClosureParts P :=
  ⟨tag, rfl⟩

/-- Relative U-substructure status of an EXACT vertex set is equivalent
before/after adding correctly tagged closure symbols and unary parts.
No expansion of the vertex set or generated hull is involved. -/
theorem isUSubstructure_iff_taggedParts
    (rules : ClosureDescription L) (A : RelStructure L V)
    (part : V → P) (S : Set V) :
    IsUSubstructure rules A S ↔
      IsUSubstructure (rules.withTaggedClosureParts P)
        (expandTaggedClosureParts rules A part) S := by
  constructor
  · intro hOld r hr t ht hRoot j
    obtain ⟨tag, htag⟩ := hr
    subst r
    exact hOld tag.rule tag.rule_mem t ht.1 hRoot j
  · intro hExpanded rule hrule t ht hRoot j
    let tag : ClosurePartTag L rules P := {
      rule := rule
      rule_mem := hrule
      rootParts := fun i => part (t (i.castLE rule.rootLE))
    }
    have hTuple :
        (expandTaggedClosureParts rules A part).rel
          (tag.liftRule.symbol) t :=
      ⟨ht, fun _ => rfl⟩
    exact hExpanded tag.liftRule tag.liftRule_mem t
      hTuple hRoot j

end RelStructure
end StructuralRamsey
