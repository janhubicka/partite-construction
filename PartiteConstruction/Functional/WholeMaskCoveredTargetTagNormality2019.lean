import PartiteConstruction.Functional.WholeMaskTagInduce2019
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Final U-closed B-covered targets have canonical full-root tags

The 2019 closure rules alone do not ensure each fresh tag is the
canonical full OLD input-root tag of its displayed complete output.
A full embedding into a normal tagged structure reflects normality,
using the already checked wholeMaskTag embedding theorem.
The final protected closed U-irreducible B-copy coverage forces
normality on the entire target by checking exact supports of the
fresh tag and old complete-value relations separately.

This is a target normalization ingredient, not a strict mixed-step
functional B-tree completion.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- A fresh full-root closure tag exactly records the canonical
complete-value OLD tuple and full induced OLD input-root embedding. -/
def WholeMaskTagNormal
    (C : RelStructure (L.wholeMaskTagLanguage P) V) : Prop :=
  ∀ (p : Language.WholeMaskRootPattern L P)
    (t : Fin (p.input.rootSize + p.mask.size) → V),
    C.rel (.inr p) t ↔
      (wholeMaskTagExpansion (wholeMaskTagReduct C)).rel (.inr p) t

/-- Canonical complete-mask tagging is normal on the original carrier. -/
theorem wholeMaskTagNormal_canonical
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) :
    WholeMaskTagNormal (wholeMaskTagExpansion E) := by
  intro p t
  rfl

/-- Full tagged embeddings pull normality back. The full input-root
pattern is displayed inside every fresh tag tuple. -/
theorem WholeMaskTagNormal.of_embedding
    {A : RelStructure (L.wholeMaskTagLanguage P) V}
    {B : RelStructure (L.wholeMaskTagLanguage P) W}
    (hB : WholeMaskTagNormal B) (e : Embedding A B) :
    WholeMaskTagNormal A := by
  intro p t
  calc
    A.rel (.inr p) t ↔ B.rel (.inr p) (e ∘ t) :=
      (e.map_rel_iff (.inr p) t).symm
    _ ↔ (wholeMaskTagExpansion (wholeMaskTagReduct B)).rel
          (.inr p) (e ∘ t) :=
      hB p (e ∘ t)
    _ ↔ (wholeMaskTagExpansion (wholeMaskTagReduct A)).rel
          (.inr p) t :=
      (e.wholeMaskTagReduct.wholeMaskTag.map_rel_iff (.inr p) t)

/-- Under final protected closed U-irreducible canonical B-copy
coverage, arbitrary U-closed tagged targets have only canonical
complete-value full-root tags. This uses no ambient hull inflation
of the weak tuple tested in either direction. -/
theorem wholeMaskTagNormal_of_closed_coverage
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
    WholeMaskTagNormal C := by
  classical
  have hLocal (S : Set V) (hIrred : (C.induce S).Irreducible) :
      WholeMaskTagNormal (C.induce S) := by
    obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
      hC hCover S hIrred
    exact (wholeMaskTagNormal_canonical
      (Base.wholeMaskPatternGraph part)).of_embedding g
  intro p t
  let S : Set V := Set.range t
  let ts : Fin (p.input.rootSize + p.mask.size) → S :=
    fun j => ⟨t j, ⟨j, rfl⟩⟩
  constructor
  · intro hTag
    have hIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C (.inr p) t hTag
    have hTagLocal : (C.induce S).rel (.inr p) ts := hTag
    have hCanLocal :
        (wholeMaskTagExpansion (wholeMaskTagReduct (C.induce S))).rel
          (.inr p) ts :=
      ((hLocal S hIrred) p ts).mp hTagLocal
    have hCanAmbientInduced :
        ((wholeMaskTagExpansion (wholeMaskTagReduct C)).induce S).rel
          (.inr p) ts :=
      (wholeMaskTagExpansion_induce_rel_iff
        (wholeMaskTagReduct C) S (.inr p) ts).mp hCanLocal
    exact hCanAmbientInduced
  · intro hCanonical
    have hOld : C.rel (.inl (.inr (.inr (p.input,p.mask)))) t :=
      hCanonical.1
    have hIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C
        (.inl (.inr (.inr (p.input,p.mask)))) t hOld
    have hCanLocal :
        (wholeMaskTagExpansion (wholeMaskTagReduct (C.induce S))).rel
          (.inr p) ts :=
      (wholeMaskTagExpansion_induce_rel_iff
        (wholeMaskTagReduct C) S (.inr p) ts).mpr hCanonical
    have hTagLocal : (C.induce S).rel (.inr p) ts :=
      ((hLocal S hIrred) p ts).mpr hCanLocal
    exact hTagLocal

end StructuralRamsey.RelStructure
