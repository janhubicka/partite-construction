import PartiteConstruction.Functional.OriginalPartialWeakImage
import PartiteConstruction.Functional.EHNProjectionGraphBridge
import PartiteConstruction.Functional.SingletonExpansion

/-!
# Exact weak-image projection for singleton-valued partial functions

This is the function-language counterpart of restricting an ordinary
relational homomorphism-embedding to a weak induced source and its exact
weak image. In the 2019 source-defined convention, a surviving output
is mapped onto the *whole* target fibre. No output-closure hull is
added and the target is NOT required to reflect undefined source inputs.

The extra singleton-fibre hypothesis is relevant: for arbitrary
multivalued functions a weak source can forget some outputs while its
projected weak image retains their labels through other vertices.

For EHN maps the original-partial fibre law below is accompanied by
the previously proved weak graph homomorphism-embedding. The pair is the
right intermediate invariant for weak tests; it does NOT assert that
every weak functional irreducible test is embedded as a full functional
substructure or that local graph-trees are strict function-trees.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- For singleton-valued sources, a partial homomorphism restricts to
a partial homomorphism of EVERY exact weak test onto its exact weak
projected image. Defined source fibres still map ONTO target fibres.
Undefined source tuples need not remain undefined under projection. -/
theorem IsOriginalPartialHomomorphism.weakImage_singleton
    {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : IsOriginalPartialHomomorphism C D p)
    (hSingle : C.SingletonValued)
    (S : Set V) :
    IsOriginalPartialHomomorphism
      (C.weakInduce S) (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  classical
  let pS : S → p '' S :=
    fun x => ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  change IsOriginalPartialHomomorphism
    (C.weakInduce S) (D.weakInduce (p '' S)) pS
  constructor
  · intro R x hx
    change D.rel R (p ∘ (Subtype.val ∘ x))
    exact hp.1 R (Subtype.val ∘ x) hx
  · intro F x hNonempty
    obtain ⟨y₀, hy₀⟩ := hNonempty
    have hDefined : (C.func F (Subtype.val ∘ x)).Nonempty :=
      ⟨y₀.1, hy₀⟩
    have hFull :
        imageSet p (C.func F (Subtype.val ∘ x)) =
          D.func F (p ∘ (Subtype.val ∘ x)) :=
      hp.2 F (Subtype.val ∘ x) hDefined
    ext z
    constructor
    · rintro ⟨y, hy, hEq⟩
      change z.1 ∈ D.func F (p ∘ (Subtype.val ∘ x))
      have hIn : p y.1 ∈ D.func F (p ∘ (Subtype.val ∘ x)) := by
        rw [← hFull]
        exact ⟨y.1, hy, rfl⟩
      have heq : z.1 = p y.1 :=
        (congrArg Subtype.val hEq).symm
      rw [heq]
      exact hIn
    · intro hz
      have hzB : z.1 ∈ D.func F (p ∘ (Subtype.val ∘ x)) := hz
      rw [← hFull] at hzB
      obtain ⟨y, hy, hEq⟩ := hzB
      have hUnique : y = y₀.1 :=
        hSingle F (Subtype.val ∘ x) y y₀.1 hy hy₀
      refine ⟨y₀, hy₀, ?_⟩
      apply Subtype.ext
      change p y₀.1 = z.1
      exact (congrArg p hUnique.symm).trans hEq

/-- Two verified projection laws combined in the natural function
language. The left law is source-defined fibre equality on weak
substructures (under singleton-valuedness); the right law protects
ordinary relational irreducibles of the weak function graph.
The projected image uses EXACTLY `p '' S`, not its closure. -/
theorem IsEHNHomomorphismEmbedding.weakImage_singleton
    {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hSingle : C.SingletonValued) (S : Set V) :
    IsOriginalPartialHomomorphism
      (C.weakInduce S) (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) ∧
    (C.weakInduce S).IsWeakHomomorphismEmbedding
      (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  have hGraph : C.IsWeakHomomorphismEmbedding D p :=
    hp.graphHomomorphismEmbedding
  exact ⟨hp.toOriginalPartial.1.weakImage_singleton hSingle S,
    hGraph.weakImage S⟩

end StructuralRamsey.Structure
