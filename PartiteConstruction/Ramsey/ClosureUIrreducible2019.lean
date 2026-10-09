import PartiteConstruction.Ramsey.ClosureSemiClosedFreeAmalgam

/-! # U-irreducibility and U-homomorphism-embeddings (2019)

This is the relational closure-description form of Definition 2.15 in
Hubička--Nešetřil, *All those Ramsey classes*.

U-irreducibility excludes free decompositions into two **proper U-closed
substructures**; it is not ordinary Gaifman irreducibility.  A
U-homomorphism-embedding is globally only a positive homomorphism and
restricts to a full embedding on **every** U-irreducible induced
substructure, including those that are not U-closed.  This last clause
is essential in published Definition 2.15: the source test must not
be assumed U-closed just because the ambient source is U-closed.

The resulting embedding-on-tests assertion is stronger than the
older, closed-tests-only experimental interface.  Vertex sets
are always induced exactly, with no U-closure hull.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- A structure is U-irreducible if it is not a free amalgam of two
proper U-closed substructures.  No U-closedness of the common root is
needed in the *definition*; it is a condition on the two sides. -/
def IsUIrreducible
    (rules : ClosureDescription L) (A : RelStructure L U) : Prop :=
  ∀ {H E F : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left A} {iR : Embedding Right A},
    IsUClosed rules Left →
    IsUClosed rules Right →
    IsFreeAmalgam sL sR iL iR →
    Function.Surjective iL ∨ Function.Surjective iR

/-- Ordinary irreducibility implies U-irreducibility.  This does not
assert the converse when U is nonempty. -/
theorem Irreducible.isUIrreducible
    {A : RelStructure L U} (hA : A.Irreducible)
    (rules : ClosureDescription L) :
    IsUIrreducible rules A := by
  intro H E F Root Left Right sL sR iL iR _ _ hFree
  have hTest :
      (A.induce (Set.range (Embedding.id A))).Irreducible :=
    hA.range_embedding (Embedding.id A)
  rcases hFree.irreducible_side
      (Set.range (Embedding.id A)) hTest with hLeft | hRight
  · left
    intro a
    obtain ⟨b, hb⟩ := hLeft ⟨a, ⟨a, rfl⟩⟩
    exact ⟨b, hb.symm⟩
  · right
    intro a
    obtain ⟨b, hb⟩ := hRight ⟨a, ⟨a, rfl⟩⟩
    exact ⟨b, hb.symm⟩

/-- A U-homomorphism-embedding in the 2019 relational sense.
The target need not be U-closed.  We quantify over *every*
U-irreducible induced substructure of the source, not only U-closed
ones; the distinction is required by Definition 2.15 (2019).
There is no global reflection requirement on arbitrary reducible
tests, but the map must reflect relation tuples on every
U-irreducible test, whether or not that test is U-closed. -/
def IsUHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L V)
    (f : U → V) : Prop :=
  A.IsHomomorphism B f ∧
    ∀ (S : Set U),
      IsUIrreducible rules (A.induce S) →
      ∃ e : Embedding (A.induce S) B,
        ∀ x, e x = f x.1

namespace IsUHomomorphismEmbedding

variable {rules : ClosureDescription L}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {f : U → V}

/-- Every U-homomorphism-embedding preserves relation tuples. -/
theorem map_rel
    (h : IsUHomomorphismEmbedding rules A B f)
    {R : L.Symbol} {x : Fin (L.arity R) → U}
    (hx : A.rel R x) :
    B.rel R (f ∘ x) :=
  h.1 R x hx

/-- The defining embedding on an exact U-irreducible test, even when
this induced test is not U-closed. -/
theorem embeddingOn
    (h : IsUHomomorphismEmbedding rules A B f)
    (S : Set U)
    (hIrred : IsUIrreducible rules (A.induce S)) :
    ∃ e : Embedding (A.induce S) B,
      ∀ x, e x = f x.1 :=
  h.2 S hIrred

/-- Convenience corollary for a U-substructure of a U-closed source.
Unlike the defining embedding-on-tests lemma, it retains the
U-closed/U-substructure parameters for callers using the older
closure-localized interface.  These hypotheses are not needed for
the published U-homomorphism-embedding condition. -/
theorem embeddingOnUSubstructure
    (h : IsUHomomorphismEmbedding rules A B f)
    (hA : IsUClosed rules A)
    (S : Set U)
    (hS : IsUSubstructure rules A S)
    (hIrred : IsUIrreducible rules (A.induce S)) :
    ∃ e : Embedding (A.induce S) B,
      ∀ x, e x = f x.1 :=
  h.embeddingOn S hIrred

end IsUHomomorphismEmbedding

/-- A full induced embedding is a U-homomorphism-embedding for every
closure description, independently of U-closedness assumptions. -/
theorem Embedding.isUHomomorphismEmbedding
    {A : RelStructure L U} {B : RelStructure L V}
    (e : Embedding A B) (rules : ClosureDescription L) :
    IsUHomomorphismEmbedding rules A B e := by
  constructor
  · intro R x hx
    exact (e.map_rel_iff R x).mpr hx
  · intro S _
    exact ⟨e.comp (inclusion A S), fun _ => rfl⟩

/-- Published Definition 2.15: a U-completion has an ordinary
irreducible target and a U-homomorphism-embedding into that target. -/
def IsUCompletion
    (rules : ClosureDescription L)
    (A : RelStructure L U) (Target : RelStructure L V) : Prop :=
  Target.Irreducible ∧
    ∃ f : U → V, IsUHomomorphismEmbedding rules A Target f

/-- A strong U-completion additionally has an injective witness map. -/
def IsStrongUCompletion
    (rules : ClosureDescription L)
    (A : RelStructure L U) (Target : RelStructure L V) : Prop :=
  Target.Irreducible ∧
    ∃ f : U → V,
      IsUHomomorphismEmbedding rules A Target f ∧
      Function.Injective f

theorem IsStrongUCompletion.isUCompletion
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (h : IsStrongUCompletion rules A B) :
    IsUCompletion rules A B := by
  obtain ⟨hIrred, f, hf, _⟩ := h
  exact ⟨hIrred, f, hf⟩

end StructuralRamsey.RelStructure
