import PartiteConstruction.Ramsey.ClosureSemiClosedFreeAmalgam

/-! # U-irreducibility and U-homomorphism-embeddings (2019)

This is the relational closure-description form of Definition 2.15 in
Hubička--Nešetřil, *All those Ramsey classes*.

U-irreducibility excludes free decompositions into two **proper U-closed
substructures**; it is not ordinary Gaifman irreducibility.  A
U-homomorphism-embedding is globally only a positive homomorphism and
restricts to a full embedding on U-closed U-irreducible substructures.

An arbitrary vertex subset of a U-closed structure need not itself be
U-closed.  Such weak tests are treated separately by the existing
U-semi-closedness interface and are never replaced by a closure hull here.
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
The target need not be U-closed; the source tests are precisely the
vertex-exact *U-closed* induced substructures.  In particular there is
no global reflection of undefined function or closure roots. -/
def IsUHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L V)
    (f : U → V) : Prop :=
  A.IsHomomorphism B f ∧
    ∀ (S : Set U),
      IsUClosed rules (A.induce S) →
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

/-- The defining embedding on an exact U-closed U-irreducible test. -/
theorem embeddingOn
    (h : IsUHomomorphismEmbedding rules A B f)
    (S : Set U)
    (hClosed : IsUClosed rules (A.induce S))
    (hIrred : IsUIrreducible rules (A.induce S)) :
    ∃ e : Embedding (A.induce S) B,
      ∀ x, e x = f x.1 :=
  h.2 S hClosed hIrred

/-- When the ambient source is U-closed, a U-substructure is already
U-closed on its exact vertex set, so the local embedding applies
without generating any new vertices. -/
theorem embeddingOnUSubstructure
    (h : IsUHomomorphismEmbedding rules A B f)
    (hA : IsUClosed rules A)
    (S : Set U)
    (hS : IsUSubstructure rules A S)
    (hIrred : IsUIrreducible rules (A.induce S)) :
    ∃ e : Embedding (A.induce S) B,
      ∀ x, e x = f x.1 :=
  h.embeddingOn S (hA.induce_of_USubstructure S hS) hIrred

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
  · intro S _ _
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
