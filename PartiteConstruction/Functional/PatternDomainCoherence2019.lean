import PartiteConstruction.Functional.PatternTagCoverageLaws2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage

/-!
# Root injectivity in noncanonical covered tagged Pictures

Canonical pattern encodings require the distinct-root tuple to be
injective. In an arbitrary U-closed tagged final Picture this does not
follow by definition: arbitrary OLD domain relation tuples could
a priori have colliding root coordinates.

The same final closed U-irreducible B-copy coverage already used for
2019 sparsening eliminates this issue. An active domain tuple has an
ordinary irreducible exact vertex support, hence its closure is
U-irreducible and embeds FULLY into a canonical tagged B. Domain
reflection in B forces injectivity on the original tuple.

No additional vertices enter the actual root being checked.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- All active OLD domain tuples of a covered U-closed tagged Picture
are injective if the same is true in its protected target.
The target need not itself be a primitive function encoding here. -/
theorem patternTag_domain_injective_of_closed_coverage
    (C : RelStructure (L.patternTag) V)
    (Target : RelStructure (L.patternTag) W)
    (hC : IsUClosed L.patternClosureRules C)
    (hTarget :
      ∀ (p : Language.FunctionInputPattern L)
        (root : Fin p.rootSize → W),
        Target.rel (.inl (.inr (.inl p))) root →
        Function.Injective root)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C → Nonempty (Embedding Test Target))
    (p : Language.FunctionInputPattern L)
    (root : Fin p.rootSize → V)
    (hDom : C.rel (.inl (.inr (.inl p))) root) :
    Function.Injective root := by
  classical
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C (.inl (.inr (.inl p))) root hDom
  obtain ⟨g⟩ :=
    weak_irreducible_embeds_base_of_closed_coverage
      hC hCover S hIrred
  let q : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hDomS :
      (C.induce S).rel (.inl (.inr (.inl p))) q := hDom
  have hDomTarget :
      Target.rel (.inl (.inr (.inl p))) (g ∘ q) :=
    (g.map_rel_iff (.inl (.inr (.inl p))) q).mpr hDomS
  have hInjTarget : Function.Injective (g ∘ q) :=
    hTarget p (g ∘ q) hDomTarget
  intro i j hij
  apply hInjTarget
  change g (q i) = g (q j)
  apply congrArg g
  exact Subtype.ext hij

/-- A canonical genuine (possibly multivalued) function structure
has only injectively enumerated active OLD domain roots. -/
theorem patternTag_domain_injective_canonical
    (Base : Structure L W)
    (p : Language.FunctionInputPattern L)
    (root : Fin p.rootSize → W)
    (h : (patternTagExpansion Base.patternGraph).rel
      (.inl (.inr (.inl p))) root) :
    Function.Injective root :=
  h.1

/-- Every OLD domain root of the final Picture has distinct vertices
when protected closed substructures embed into a canonical tagged
primitive-function Base. This does not assume the Picture is already
the canonical expansion of its decoded reduct. -/
theorem patternTag_domain_injective_of_canonical_coverage
    (C : RelStructure (L.patternTag) V) (Base : Structure L W)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph)))
    (p : Language.FunctionInputPattern L)
    (root : Fin p.rootSize → V)
    (hDom : C.rel (.inl (.inr (.inl p))) root) :
    Function.Injective root :=
  patternTag_domain_injective_of_closed_coverage C
    (patternTagExpansion Base.patternGraph) hC
    (patternTag_domain_injective_canonical Base) hCover p root hDom

end StructuralRamsey.RelStructure
