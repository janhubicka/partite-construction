import PartiteConstruction.Functional.WeakSingletonPartialProjection

/-!
# Ambient-closed tests inside weak functional substructures

A weak vertex restriction can make a previously defined function
undefined by forgetting its output. Therefore it would be false to
demand that EVERY intrinsically irreducible weak test embed fully into a
strict functional B-tree: even a singleton with a forgotten unary output
can violate that requirement.

The useful invariant instead protects exactly those irreducible
substructures whose map into the ORIGINAL ambient C is a full functional
embedding (and hence has function-closed image), plus positive
source-defined partial-function preservation on the weak source.

For a genuinely closed S, every full irreducible embedding into
C.induce S composes to such an ambient full embedding. Thus the
ambient-relative predicate reduces to the ordinary original-2019
homomorphism-embedding on the closed test.

EHN projections satisfy this predicate for EVERY weak set S in the
singleton-valued (ranked partial function) language, with target the
EXACT weak image p[S]. Neither source nor image is enlarged to a hull.
This is a local projection interface, not a strict target-tree
construction theorem.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- A weak substructure map which behaves as a genuine partial
homomorphism on retained function inputs and preserves all *ambient*
full irreducible embedded copies. Only genuinely embedded original
pieces are protected, not spurious intrinsically irreducible tests
formed by deleting function outputs from the weak source. -/
def IsAmbientWeakOriginalPartialHE
    (C : Structure L U) (S : Set U)
    (T : Structure L V) (f : S → V) : Prop :=
  IsOriginalPartialHomomorphism (C.weakInduce S) T f ∧
  ∀ {X : Type v} (E : Structure L X), E.Irreducible →
    ∀ (e : Embedding E C) (he : ∀ x, e x ∈ S),
      ∃ g : Embedding E T,
        ∀ x, g x = f ⟨e x, he x⟩

/-- On a genuinely function-closed S this ambient-relative weak
interface is an ordinary original-2019 partial homomorphism-embedding.
The source has EXACTLY S as its carrier, without a generated hull. -/
theorem IsAmbientWeakOriginalPartialHE.toOriginalPartialHE_of_closed
    {C : Structure L U} {S : Set U} {T : Structure L V}
    {f : S → V}
    (h : IsAmbientWeakOriginalPartialHE C S T f)
    (hS : C.IsClosed S) :
    IsOriginalPartialHomomorphismEmbedding (C.induce S hS) T f := by
  refine ⟨?_, ?_⟩
  · change IsOriginalPartialHomomorphism (C.weakInduce S) T f
    exact h.1
  · intro X E hE e
    let inc : Embedding (C.induce S hS) C := inclusion C S hS
    let eC : Embedding E C := inc.comp e
    have heC : ∀ x, eC x ∈ S := fun x => (e x).property
    obtain ⟨g, hg⟩ := h.2 E hE eC heC
    refine ⟨g, ?_⟩
    intro x
    calc
      g x = f ⟨eC x, heC x⟩ := hg x
      _ = f (e x) := by
        congr 1
        apply Subtype.ext
        rfl

/-- Under singleton-valuedness an EHN original-partial projection
satisfies the ambient-relative weak homomorphism-embedding interface
for *every* exact weak source and exact weak projected image. Full
functional irreducible ambient pieces retain genuine target embeddings. -/
theorem IsEHNHomomorphismEmbedding.ambientWeakImage_singleton
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hSingle : C.SingletonValued) (S : Set U) :
    IsAmbientWeakOriginalPartialHE C S
      (D.weakInduce (p '' S))
      (fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  constructor
  · exact hp.toOriginalPartial.1.weakImage_singleton hSingle S
  · intro X E hE e he
    obtain ⟨g, hg⟩ := hp.2 E hE e
    have hgRange : ∀ x, g x ∈ p '' S := by
      intro x
      rw [hg x]
      exact ⟨e x, he x, rfl⟩
    let gWeak : Embedding E (D.weakInduce (p '' S)) :=
      g.codRestrictWeak (p '' S) hgRange
    refine ⟨gWeak, ?_⟩
    intro x
    apply Subtype.ext
    exact hg x

end StructuralRamsey.Structure
