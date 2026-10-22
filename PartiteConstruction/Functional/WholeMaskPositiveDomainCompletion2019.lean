import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019
import PartiteConstruction.Functional.WholeMaskActiveRootExtraction
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019

/-!
# An active positive complete-output mask has its full tuple in a U-closed target

A fresh complete-mask U-closure tag records the FULL OLD induced
pattern of an active injective input root. If both the primitive
input root and the complete output mask are nonempty, the prescribed
2019 closure rule applies to that root. U-closedness supplies one
full tagged closure tuple; tag normality converts it back to an OLD
complete-value tuple with the EXACT same input vertices.

This is a direct genuinely partial-function domain -> whole output
existence theorem in the final noncanonical tagged TARGET. It neither
assumes a canonical target before proving normality nor inserts
additional vertices into an exact weak source test.

For zero-output masks no new vertices are required, but preserving
defined-empty is independent of the positive 2019 closure rules
(handled by the separate covered-target theorem). Nullary inputs
likewise require a separate root-free treatment.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V : Type v}

/-- Under full-root tag normality and 2019 U-closedness, each
injective positive OLD input root with an active NONEMPTY complete
output-part mask has an entire OLD complete-value tuple with that
same input root. The target may otherwise be noncanonical. -/
theorem WholeMaskTagNormal.positiveDomain_has_completeValue
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (hNormal : WholeMaskTagNormal C)
    (hClosed : IsUClosed (L.wholeMaskClosureRules P) C)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (hp : 0 < p.rootSize) (hq : 0 < q.size)
    (root : Fin p.rootSize → V)
    (hInj : Function.Injective root)
    (hDomain : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q))) root) :
    ∃ t : Fin (p.rootSize + q.size) → V,
      (wholeMaskTagReduct C).rel (.inr (.inr (p,q))) t ∧
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd q.size i) = root i := by
  classical
  let E := wholeMaskTagReduct C
  let pat : Language.WholeMaskRootPattern L P :=
    Language.WholeMaskRootPattern.ofActiveDomain
      E p q hp hq root hDomain
  let oldRoot : Embedding pat.root E :=
    Language.WholeMaskRootPattern.ofActiveDomain_embedding
      E p q hp hq root hInj hDomain
  let canonicalIntoC : Embedding (wholeMaskTagExpansion E) C := {
    toFun := id
    injective := Function.injective_id
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R => exact Iff.rfl
      | inr tag =>
          simpa only [Function.id_comp] using hNormal tag xs
  }
  let taggedRoot : Embedding pat.closureRule.root C :=
    canonicalIntoC.comp oldRoot.wholeMaskTag
  obtain ⟨t, ht, _⟩ :=
    (hClosed pat.closureRule ⟨pat, rfl⟩).2 taggedRoot
  have hOld : E.rel (.inr (.inr (p,q))) t :=
    ((hNormal pat t).mp ht.1).1
  refine ⟨t, hOld, ?_⟩
  intro i
  have h := ht.2 i
  have hIdx : i.castLE pat.closureRule.rootLE =
      Fin.castAdd q.size i := by
    apply Fin.ext
    rfl
  rw [hIdx] at h
  change t (Fin.castAdd q.size i) = root i at h
  exact h

end StructuralRamsey.RelStructure
