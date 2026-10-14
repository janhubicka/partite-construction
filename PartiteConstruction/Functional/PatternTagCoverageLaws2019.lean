import PartiteConstruction.Functional.PatternTagLocalLaws2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Derive 2019 function-tag normality from closed B-copy coverage

A U-closed tagged Picture need not itself be canonical. Nevertheless,
if every U-closed U-irreducible induced test of C embeds into an
already NORMAL, output-root-VALID tagged Base, then every ordinary
irreducible weak induced test also embeds into Base, by the proved
irreducible-seed closure lemma.

Both fresh-tag normality and old output-domain validity are tuple-
local laws. For a positive relation or its complete-root tag, its
exact tuple support is ordinarily irreducible and is therefore covered
by Base. Transport the two laws to that support and back through the
canonical induced embedding. No source test grows when the local
law is applied, and no arbitrary incompatible completion is chosen.

This is the direct function-root analogue of the verified 2019
profileTag2019_local_laws_of_closed_coverage theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- The essential local laws hold throughout a final U-closed
tagged Picture if every protected closed U-irreducible test
fully embeds into a canonical/normal, root-valid Base. -/
theorem patternTag_local_laws_of_closed_coverage
    (C : RelStructure (L.patternTag) V)
    (Base : RelStructure (L.patternTag) W)
    (hC : IsUClosed (L.patternClosureRules) C)
    (hBaseNormal : PatternTagNormal Base)
    (hBaseValid : PatternTagGraphRootValid Base)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed (L.patternClosureRules) Test →
      IsUIrreducible (L.patternClosureRules) Test →
      Embedding Test C → Nonempty (Embedding Test Base)) :
    PatternTagNormal C ∧ PatternTagGraphRootValid C := by
  classical
  have hLocal : ∀ S : Set V, (C.induce S).Irreducible →
      PatternTagNormal (C.induce S) ∧
        PatternTagGraphRootValid (C.induce S) := by
    intro S hIrred
    obtain ⟨e⟩ :=
      weak_irreducible_embeds_base_of_closed_coverage
        hC hCover S hIrred
    exact ⟨hBaseNormal.of_embedding e,
      hBaseValid.of_embedding e⟩
  constructor
  · intro p t
    let S : Set V := Set.range t
    let ts : Fin (p.input.rootSize + 1) → S :=
      fun i => ⟨t i, ⟨i, rfl⟩⟩
    let inc := inclusion C S
    let incOld := Embedding.patternTagReduct inc
    let incTag := Embedding.patternTag incOld
    constructor
    · intro ht
      have hIrred : (C.induce S).Irreducible :=
        relationTuple_range_irreducible C (.inr p) t ht
      have hLocalTag :
          (C.induce S).rel (.inr p) ts := ht
      have hCanonicalLocal :=
        ((hLocal S hIrred).1 p ts).mp hLocalTag
      have hCanonicalGlobal :=
        (incTag.map_rel_iff (.inr p) ts).mpr hCanonicalLocal
      exact hCanonicalGlobal
    · intro ht
      have hOld : C.rel (.inl (.inr (.inr p.input))) t := ht.1
      have hIrred : (C.induce S).Irreducible :=
        relationTuple_range_irreducible C
          (.inl (.inr (.inr p.input))) t hOld
      have hCanonicalLocal :=
        (incTag.map_rel_iff (.inr p) ts).mp ht
      have hTagLocal := ((hLocal S hIrred).1 p ts).mpr
        hCanonicalLocal
      exact hTagLocal
  · intro p t ht
    let S : Set V := Set.range t
    let ts : Fin (p.rootSize + 1) → S :=
      fun i => ⟨t i, ⟨i, rfl⟩⟩
    have hIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C
        (.inl (.inr (.inr p))) t ht
    have hOldLocal :
        (patternTagReduct (C.induce S)).rel
          (.inr (.inr p)) ts := ht
    have hDomLocal :=
      (hLocal S hIrred).2 p ts hOldLocal
    let incOld := Embedding.patternTagReduct (inclusion C S)
    have hDomGlobal :=
      (incOld.map_rel_iff (.inr (.inl p))
        (fun i : Fin p.rootSize => ts i.castSucc)).mpr hDomLocal
    exact hDomGlobal

end StructuralRamsey.RelStructure
