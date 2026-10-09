import PartiteConstruction.Ramsey.ClosureUIrreducible2019
import PartiteConstruction.Ramsey.CompletionTransfer

/-! # Maps protecting closed U-irreducible tests

This is an explicitly named WORKING convention for the positive proof.
It is not a redefinition of `IsUHomomorphismEmbedding` from the literal
2019 audit. Relating the convention to Definition 2.17 remains separate.

Tests are represented by embeddings of a U-closed U-irreducible structure,
not by its particular subtype carrier. This makes composition and source
restriction transparent: the same test embeds into the larger source.
An arbitrary weak source restriction may omit outputs, but its protected
closed tests are still protected in the ambient source.

All maps are positive relational homomorphisms. They need not be globally
injective, reflect absent tuples globally, or send a weak image to a
U-closed vertex set.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- Positive map which is a full embedding on each embedded U-closed,
U-irreducible test. The word `Closed` records the additional test
qualification; the literal 2019 predicate is left unchanged. -/
def IsClosedUHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L V)
    (f : U → V) : Prop :=
  A.IsHomomorphism B f ∧
    ∀ {E : Type v} (Test : RelStructure L E),
      IsUClosed rules Test → IsUIrreducible rules Test →
      ∀ e : Embedding Test A,
        ∃ g : Embedding Test B, ∀ x, g x = f (e x)

namespace IsClosedUHomomorphismEmbedding

variable {rules : ClosureDescription L}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W}
variable {f : U → V} {g : V → W}

/-- The exact embedding on a protected source test. -/
theorem on_test
    (h : IsClosedUHomomorphismEmbedding rules A B f)
    {E : Type v} (Test : RelStructure L E)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : Embedding Test A) :
    ∃ j : Embedding Test B, ∀ x, j x = f (e x) :=
  h.2 Test hClosed hIrred e

/-- Composition keeps the ORIGINAL protected test carrier. No image
closedness assertion and no isomorphism-transport oracle is needed. -/
theorem comp
    (hg : IsClosedUHomomorphismEmbedding rules B C g)
    (hf : IsClosedUHomomorphismEmbedding rules A B f) :
    IsClosedUHomomorphismEmbedding rules A C (g ∘ f) := by
  constructor
  · intro R x hx
    exact hg.1 R (f ∘ x) (hf.1 R x hx)
  · intro E Test hClosed hIrred e
    obtain ⟨j, hj⟩ := hf.on_test Test hClosed hIrred e
    obtain ⟨k, hk⟩ := hg.on_test Test hClosed hIrred j
    refine ⟨k, ?_⟩
    intro x
    exact (hk x).trans (congrArg g (hj x))

/-- Precomposition by any full RELATIONAL embedding. Its source need
not be U-closed. In particular arbitrary weak induced tests are allowed. -/
theorem precomp_embedding
    (h : IsClosedUHomomorphismEmbedding rules A B f)
    {E : Type v} {Source : RelStructure L E}
    (e : Embedding Source A) :
    IsClosedUHomomorphismEmbedding rules Source B (f ∘ e) := by
  constructor
  · intro R x hx
    exact h.1 R (e ∘ x) ((e.map_rel_iff R x).mpr hx)
  · intro Z Test hClosed hIrred a
    exact h.on_test Test hClosed hIrred (e.comp a)

/-- Restrict the target to an exact induced vertex set containing the
range. This target set is NOT required to be U-closed. -/
theorem codRestrict
    (h : IsClosedUHomomorphismEmbedding rules A B f)
    (S : Set V) (hS : ∀ a, f a ∈ S) :
    IsClosedUHomomorphismEmbedding rules A (B.induce S)
      (fun a => (⟨f a, hS a⟩ : S)) := by
  constructor
  · intro R x hx
    exact h.1 R x hx
  · intro E Test hClosed hIrred e
    obtain ⟨j, hj⟩ := h.on_test Test hClosed hIrred e
    let k : Embedding Test (B.induce S) := {
      toFun := fun x => ⟨j x, by rw [hj x]; exact hS (e x)⟩
      injective := by
        intro x y hxy
        exact j.injective (congrArg (fun z : S => z.1) hxy)
      map_rel_iff := fun R x => j.map_rel_iff R x
    }
    refine ⟨k, ?_⟩
    intro x
    exact Subtype.ext (hj x)

/-- Weak source and weak image restriction, with exactly S and f[S].
The theorem does not generate either closure hull. -/
theorem weakImage
    (h : IsClosedUHomomorphismEmbedding rules A B f)
    (S : Set U) :
    IsClosedUHomomorphismEmbedding rules (A.induce S)
      (B.induce (f '' S))
      (fun x : S => (⟨f x.1, ⟨x.1, x.2, rfl⟩⟩ : f '' S)) := by
  have hs := h.precomp_embedding (inclusion A S)
  exact hs.codRestrict (f '' S) (fun x => ⟨x.1, x.2, rfl⟩)

/-- A protected fixed structure gives copywise preservation directly. -/
theorem copywise
    (h : IsClosedUHomomorphismEmbedding rules A B f)
    (Test : RelStructure L X)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test) :
    CopywiseCompletion Test A B f :=
  h.2 Test hClosed hIrred

end IsClosedUHomomorphismEmbedding

/-- Full embeddings satisfy the working closed-test map condition. -/
theorem Embedding.isClosedUHomomorphismEmbedding
    {A : RelStructure L U} {B : RelStructure L V}
    (e : Embedding A B) (rules : ClosureDescription L) :
    IsClosedUHomomorphismEmbedding rules A B e := by
  constructor
  · intro R x hx
    exact (e.map_rel_iff R x).mpr hx
  · intro E Test _ _ a
    exact ⟨e.comp a, fun _ => rfl⟩

end StructuralRamsey.RelStructure
