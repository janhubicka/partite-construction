import PartiteConstruction.Functional.WholeMaskTagFreeAmalgam2019
import PartiteConstruction.Functional.WholeMaskActiveRootExtraction

/-!
# Complete-mask domain coherence survives source free amalgamation

The 2019 closure rules control the complete output tuple separately for
each OLD active domain mask. They do not, by themselves, forbid two
different masks on the SAME primitive function arguments.

Canonical genuinely partial function sources satisfy this additional OLD
law: two active domain masks on one DISTINCT input root have equal sets
of output-part labels. This module shows the law is exact-hereditary and
stable under a genuine free amalgam of FULL OLD relational embeddings.

In the mixed case, both domain tuples have the same entire input root.
One root tuple lies on each side; the exact intersection property forces
each input vertex into the common root. Both domain tuples then reflect
to that common root, where mask coherence can be invoked. No closure
vertices or target function decoding are introduced.

Target completion must still guarantee EXISTENCE/uniqueness/coherence of
complete output tuples for its old active masks; the law proved here is
one necessary component, not arbitrary tagged target normalization.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V : Type v}

/-- One primitive input equality-pattern root cannot activate two
different complete SETS of output parts. Their enumeration orders
may differ, and this is therefore equality of ranges, not labels. -/
def HasUniqueWholeMaskDomainSets
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (q₁ q₂ : Language.CompleteOutputParts P)
    (root : Fin p.rootSize → V),
      E.rel (.inr (.inl (p, q₁))) root →
      E.rel (.inr (.inl (p, q₂))) root →
      Set.range q₁.label = Set.range q₂.label

/-- Every canonical complete-value OLD relational source remembers a
unique OUTPUT-PART SET over each defined primitive input, even though
the OLD language allows different enumerations of that set. -/
theorem PartialSetStructure.wholeMaskPatternGraph_uniqueDomainSets
    (A : PartialSetStructure L V) (part : V → P) :
    HasUniqueWholeMaskDomainSets (A.wholeMaskPatternGraph part) := by
  intro p q₁ q₂ root h₁ h₂
  exact A.wholeMaskPatternGraph_domain_mask_set_unique
    part p q₁ q₂ root h₁ h₂

/-- Coherence of ambient old domain masks survives exact induced weak
restriction. Unlike the native restricted function, ambient mask-domain
tuples are NOT dropped when a whole output value escapes the subset. -/
theorem HasUniqueWholeMaskDomainSets.induce
    {E : RelStructure (L.wholeMaskPatternLanguage P) V}
    (h : HasUniqueWholeMaskDomainSets E) (S : Set V) :
    HasUniqueWholeMaskDomainSets (E.induce S) := by
  intro p q₁ q₂ root h₁ h₂
  exact h p q₁ q₂ (Subtype.val ∘ root) h₁ h₂

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {H E F C : Type v}

/-- The OLD complete-mask domain uniqueness law survives an actual
free amalgam of FULL OLD relational embeddings, because domain-root
tuples on opposite sides have their entire roots in the shared base. -/
theorem wholeMaskDomainSetsCoherent
    {Root : RelStructure (L.wholeMaskPatternLanguage P) H}
    {Left : RelStructure (L.wholeMaskPatternLanguage P) E}
    {Right : RelStructure (L.wholeMaskPatternLanguage P) F}
    {Whole : RelStructure (L.wholeMaskPatternLanguage P) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : HasUniqueWholeMaskDomainSets Root)
    (hLeft : HasUniqueWholeMaskDomainSets Left)
    (hRight : HasUniqueWholeMaskDomainSets Right) :
    HasUniqueWholeMaskDomainSets Whole := by
  classical
  have hCross (p : Language.FunctionInputPattern L)
      (q₁ q₂ : Language.CompleteOutputParts P)
      (a : Fin p.rootSize → E) (b : Fin p.rootSize → F)
      (ha : Left.rel (.inr (.inl (p,q₁))) a)
      (hb : Right.rel (.inr (.inl (p,q₂))) b)
      (hab : iL ∘ a = iR ∘ b) :
      Set.range q₁.label = Set.range q₂.label := by
    have hShared (j : Fin p.rootSize) :
        ∃ x : H, a j = sL x ∧ b j = sR x :=
      (hFree.overlap (a j) (b j)).mp (congrFun hab j)
    let root : Fin p.rootSize → H :=
      fun j => Classical.choose (hShared j)
    have hLa : a = sL ∘ root := by
      funext j
      exact (Classical.choose_spec (hShared j)).1
    have hRb : b = sR ∘ root := by
      funext j
      exact (Classical.choose_spec (hShared j)).2
    have h₁ : Root.rel (.inr (.inl (p,q₁))) root := by
      apply (sL.map_rel_iff (.inr (.inl (p,q₁))) root).mp
      change Left.rel (.inr (.inl (p,q₁))) (sL ∘ root)
      rw [← hLa]
      exact ha
    have h₂ : Root.rel (.inr (.inl (p,q₂))) root := by
      apply (sR.map_rel_iff (.inr (.inl (p,q₂))) root).mp
      change Right.rel (.inr (.inl (p,q₂))) (sR ∘ root)
      rw [← hRb]
      exact hb
    exact hRoot p q₁ q₂ root h₁ h₂
  intro p q₁ q₂ z hz₁ hz₂
  rcases (hFree.rel_iff (.inr (.inl (p,q₁))) z).mp hz₁ with
    ⟨a₁, ha₁, hza₁⟩ | ⟨b₁, hb₁, hzb₁⟩
  · rcases (hFree.rel_iff (.inr (.inl (p,q₂))) z).mp hz₂ with
      ⟨a₂, ha₂, hza₂⟩ | ⟨b₂, hb₂, hzb₂⟩
    · have heq : a₁ = a₂ := by
        funext j
        apply iL.injective
        exact (congrFun hza₁ j).symm.trans (congrFun hza₂ j)
      rw [← heq] at ha₂
      exact hLeft p q₁ q₂ a₁ ha₁ ha₂
    · exact hCross p q₁ q₂ a₁ b₂ ha₁ hb₂
        (hza₁.symm.trans hzb₂)
  · rcases (hFree.rel_iff (.inr (.inl (p,q₂))) z).mp hz₂ with
      ⟨a₂, ha₂, hza₂⟩ | ⟨b₂, hb₂, hzb₂⟩
    · exact (hCross p q₂ q₁ a₂ b₁ ha₂ hb₁
        (hza₂.symm.trans hzb₁)).symm
    · have heq : b₁ = b₂ := by
        funext j
        apply iR.injective
        exact (congrFun hzb₁ j).symm.trans (congrFun hzb₂ j)
      rw [← heq] at hb₂
      exact hRight p q₁ q₂ b₁ hb₁ hb₂

end StructuralRamsey.RelStructure.IsFreeAmalgam
