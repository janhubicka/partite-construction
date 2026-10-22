import PartiteConstruction.Functional.WholeMaskDomainCoherenceFreeAmalgam2019
import PartiteConstruction.Functional.WholeMaskRelativeClosure2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Protected B-copy coverage forces correct OLD domain records in targets

The canonical genuine partial-function complete-mask graph has two local
OLD properties: each complete-value tuple has an injective distinct-input
root and its active domain-mask tuple; and two active masks on the SAME
root have the same underlying output-part SET.

U-closedness of a tagged target alone does not imply either property.
But the protected B-copy coverage invariant for the FINAL 2019
construction does: the vertex support of each domain or output tuple
is ordinarily irreducible, so the verified closed-irreducible coverage
lemma embeds that exact weak support into a canonical B. Full
reflection of old relations transfers the canonical local laws back.
We do not replace any weak test by its ambient hull.

These are conditions for normalizing final targets. They do not claim
arbitrary mixed intermediate Pictures admit strict full-functional
B-tree completions or that the remaining cross-pattern output
coherence has been established.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- The protected final-copy coverage supplies the OLD uniqueness of
active output-part SETS on every exact root of the tagged target.
No compatibility hypothesis is assumed about the target in advance. -/
theorem wholeMask_domainSets_coherent_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part)))) :
    HasUniqueWholeMaskDomainSets (wholeMaskTagReduct C) := by
  classical
  intro p q₁ q₂ root h₁ h₂
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q₁)))) root h₁
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let rS : Fin p.rootSize → S := fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hS₁ : (C.induce S).rel (.inl (.inr (.inl (p,q₁)))) rS := h₁
  have hS₂ : (C.induce S).rel (.inl (.inr (.inl (p,q₂)))) rS := h₂
  have hB₁ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inl (p,q₁))) (g ∘ rS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q₁)))) rS).mpr hS₁
  have hB₂ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inl (p,q₂))) (g ∘ rS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q₂)))) rS).mpr hS₂
  exact Base.wholeMaskPatternGraph_domain_mask_set_unique
    part p q₁ q₂ (g ∘ rS) hB₁ hB₂

/-- Every output tuple in the OLD reduct of a final covered tagged
target has an injective root and the corresponding OLD domain
relation. This includes empty output lists and repeated original
primitive function arguments (the distinct root itself is injective). -/
theorem wholeMask_validCompleteDomains_of_closed_coverage
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part)))) :
    HasValidCompleteMaskDomains (wholeMaskTagReduct C) := by
  classical
  intro p q t ht
  let S : Set V := Set.range t
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inr (p,q)))) t ht
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let ts : Fin (p.rootSize + q.size) → S :=
    fun j => ⟨t j, ⟨j, rfl⟩⟩
  have hST : (C.induce S).rel (.inl (.inr (.inr (p,q)))) ts := ht
  have hBT : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p,q))) (g ∘ ts) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) ts).mpr hST
  obtain ⟨hInjectiveB, hDomainB⟩ :=
    StructuralRamsey.RelStructure.PartialSetStructure.wholeMaskPatternGraph_validDomains
      Base part p q
      (g ∘ ts) hBT
  let rS : Fin p.rootSize → S :=
    fun i => ts (Fin.castAdd q.size i)
  have hInjective : Function.Injective
      (fun i : Fin p.rootSize => t (Fin.castAdd q.size i)) := by
    intro i j hij
    apply hInjectiveB
    change g (rS i) = g (rS j)
    exact congrArg g (Subtype.ext hij)
  have hBaseDomain :
      (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part)).rel
        (.inl (.inr (.inl (p,q)))) (g ∘ rS) := by
    change (Base.wholeMaskPatternGraph part).rel
      (.inr (.inl (p,q))) (g ∘ rS)
    exact hDomainB
  have hLocal : (C.induce S).rel
      (.inl (.inr (.inl (p,q)))) rS :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rS).mp
      hBaseDomain
  have hAmbient : C.rel (.inl (.inr (.inl (p,q))))
      (Subtype.val ∘ rS) := hLocal
  exact ⟨hInjective, hAmbient⟩

end StructuralRamsey.RelStructure
