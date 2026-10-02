import PartiteConstruction.Partite.InducedInvariant

/-! # Projected irreducible coverage

This isolates the invariant used when iterating the induced construction all
the way back to the original Ramsey witness.  A map \`p : C → Q\` covers
irreducibles by \`B\` when the image of every irreducible induced substructure
of \`C\` is contained in an embedded copy of \`B\` in \`Q\`.

The key composition fact is one-sided: if \`C\` homomorphism-embeds into \`D\`
and the map from \`D\` to \`Q\` already covers irreducibles, then the composite
also covers irreducibles.  The first map turns an irreducible source into a
genuine embedded irreducible image.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W X Y : Type v}

/-- Every irreducible induced substructure of \`C\` projects into a copy of
\`B\` in \`Q\`. -/
def ProjectsIrreduciblesInto
    (B : RelStructure L V) (C : RelStructure L W)
    (Q : RelStructure L Y) (p : W → Y) : Prop :=
  ∀ (S : Set W), (C.induce S).Irreducible →
    ∃ β : Embedding B Q,
      ∀ z : S, ∃ b : V, p z.1 = β b

namespace ProjectsIrreduciblesInto

/-- Pull projected irreducible coverage back through a
homomorphism-embedding. -/
theorem precomp
    {B : RelStructure L V} {C : RelStructure L W}
    {D : RelStructure L X} {Q : RelStructure L Y}
    {p : W → X} {q : X → Y}
    (hp : C.IsHomomorphismEmbedding D p)
    (hq : ProjectsIrreduciblesInto B D Q q) :
    ProjectsIrreduciblesInto B C Q (q ∘ p) := by
  classical
  intro S hS
  obtain ⟨e, he⟩ := hp.embeddingOn S hS
  let Rng : Set X := Set.range e
  have hRng : (D.induce Rng).Irreducible :=
    hS.range_embedding e
  obtain ⟨β, hβ⟩ := hq Rng hRng
  refine ⟨β, ?_⟩
  intro z
  let r : Rng := ⟨e z, ⟨z, rfl⟩⟩
  obtain ⟨b, hb⟩ := hβ r
  refine ⟨b, ?_⟩
  change q (p z.1) = β b
  calc
    q (p z.1) = q (e z) := congrArg q (he z).symm
    _ = β b := hb

end ProjectsIrreduciblesInto

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V P X : Type v}

/-- The partite invariant (3) is exactly projected irreducible coverage for
the partition map. -/
theorem projectsIrreduciblesInto_of_covers
    (B : RelStructure L V) (D : RelStructure L P)
    (C : Partite.System L P X)
    (h : CoversIrreduciblesBy C B D) :
    RelStructure.ProjectsIrreduciblesInto
      B C.toRelStructure D C.part :=
  h

end StructuralRamsey.Partite.Induced
