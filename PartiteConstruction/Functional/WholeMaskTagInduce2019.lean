import PartiteConstruction.Functional.WholeMaskClosureTags2019
import PartiteConstruction.Functional.PatternLanguageFinite

/-!
# Full-root complete-mask tagging commutes with exact induced restriction

The fresh 2019 closure tag on a tuple carries a full embedding of its
distinct input-root pattern, but ALL root vertices are displayed in the
tuple prefix. Consequently such an ambient root embedding restricts to
the exact induced carrier whenever the tuple lies there. No closure
vertices are added. The converse is immediate via full inclusion.

This is the missing structural bridge between persistent ambient tags
and exact weak tests. It does not claim that a weak partial-function
operation retains ambient domain masks.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Canonical full-root tags commute relation-by-relation with inducing
on an arbitrary EXACT vertex subset S. In particular the domain masks
of the OLD induced language are inherited from the ambient structure. -/
theorem wholeMaskTagExpansion_induce_rel_iff
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (S : Set V)
    (R : (L.wholeMaskTagLanguage P).Symbol)
    (xs : Fin ((L.wholeMaskTagLanguage P).arity R) → S) :
    (wholeMaskTagExpansion (E.induce S)).rel R xs ↔
      ((wholeMaskTagExpansion E).induce S).rel R xs := by
  cases R with
  | inl R =>
      rfl
  | inr p =>
      change
        (E.rel (.inr (.inr (p.input,p.mask))) (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root (E.induce S),
            ∀ i : Fin p.input.rootSize,
              xs (Fin.castAdd p.mask.size i) = g i) ↔
        (E.rel (.inr (.inr (p.input,p.mask))) (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              (Subtype.val ∘ xs) (Fin.castAdd p.mask.size i) = g i)
      constructor
      · rintro ⟨hOld,g,hPrefix⟩
        refine ⟨hOld, (inclusion E S).comp g, ?_⟩
        intro i
        exact congrArg Subtype.val (hPrefix i)
      · rintro ⟨hOld,g,hPrefix⟩
        let e : Fin p.input.rootSize → S :=
          fun i => ⟨g i, by
            rw [← hPrefix i]
            exact (xs (Fin.castAdd p.mask.size i)).2⟩
        let gS : Embedding p.root (E.induce S) := {
          toFun := e
          injective := by
            intro i j hij
            apply g.injective
            exact congrArg Subtype.val hij
          map_rel_iff := by
            intro R ys
            change E.rel R (g ∘ ys) ↔ p.root.rel R ys
            exact g.map_rel_iff R ys
        }
        refine ⟨hOld, gS, ?_⟩
        intro i
        apply Subtype.ext
        exact hPrefix i

/-- Literal equality of the tagged induced ambient structure and the
canonical tagged expansion of the OLD induced structure. -/
theorem wholeMaskTagExpansion_induce_eq
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (S : Set V) :
    wholeMaskTagExpansion (E.induce S) =
      (wholeMaskTagExpansion E).induce S := by
  apply rel_injective
  funext R xs
  exact propext (wholeMaskTagExpansion_induce_rel_iff E S R xs)

end StructuralRamsey.RelStructure
