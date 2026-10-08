import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-! # Homomorphisms of genuinely partial functions: the 2019 convention

In Hubička--Nešetřil, *All those Ramsey classes* (2019),
a function symbol is a partial map
  F_A : Dom(F_A) ⊆ A^r → A.
A homomorphism sends defined tuples to defined tuples and preserves
their values, but does NOT reflect whether an arbitrary source tuple
is in the function domain. An embedding additionally reflects the
function domain.

We model partial (possibly set-valued, nonempty-valued) operations using
the existing `Structure` representation by defining the domain of
F_A to consist of tuples whose fibre `A.func F x` is NONEMPTY.
This exactly encodes the single-valued partial functions of the 2019
paper. It does not encode the more general distinction between a
*defined empty set-valued value* and an undefined tuple; that would
require an independent domain predicate or `Option (Set A)`.

The later survey's `Structure.IsHomomorphism` is different: its total
set-valued fibres must be equal for ALL tuples, so it reflects domain
nonemptiness. Crucially, the already-checked EHN fibre-exactness lemma
shows that the EHN weak projection satisfies precisely the original
2019 notion, including equality on every *defined* source fibre.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- The defined inputs of the partial operation encoded by a
nonempty-valued set-valued fibre. In the 2019 single-valued case this
is exactly the domain of the original partial function. -/
def InOriginalPartialDomain (A : Structure L U)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → U) : Prop :=
  (A.func F x).Nonempty

/-- Original partial-function homomorphism convention: preserve
ordinary relations and map the *whole fibre* onto the target fibre
whenever the source input is defined. Nothing is required when its
source input is outside the function domain. -/
def IsOriginalPartialHomomorphism
    (A : Structure L U) (B : Structure L V) (f : U → V) : Prop :=
  (∀ R x, A.rel R x → B.rel R (f ∘ x)) ∧
  (∀ F x, InOriginalPartialDomain A F x →
    imageSet f (A.func F x) = B.func F (f ∘ x))

/-- Any original-style partial homomorphism preserves every witnessed
function incidence in the existing weak functional interface. -/
theorem IsOriginalPartialHomomorphism.toWeak
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : IsOriginalPartialHomomorphism A B f) :
    A.IsWeakHomomorphism B f := by
  constructor
  · exact hf.1
  · intro F x y hy
    have himg : f y ∈ imageSet f (A.func F x) :=
      ⟨y, hy, rfl⟩
    rw [hf.2 F x ⟨y, hy⟩] at himg
    exact himg

/-- A partial homomorphism-embedding is a 2019 partial homomorphism
which restricts to a full embedding on each irreducible full
substructure of its source. This is the literal functional analogue
of the 2019 Definition 2.3. -/
def IsOriginalPartialHomomorphismEmbedding
    (A : Structure L U) (B : Structure L V) (f : U → V) : Prop :=
  IsOriginalPartialHomomorphism A B f ∧
  ∀ {X : Type v} (E : Structure L X), E.Irreducible →
    ∀ e : Embedding E A,
      ∃ g : Embedding E B, ∀ x, g x = f (e x)

/-- The native EHN projection already preserves the entire target
fibre at every *defined* input. No global domain reflection needed. -/
theorem IsEHNHomomorphismEmbedding.toOriginalPartial
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : A.IsEHNHomomorphismEmbedding B f) :
    IsOriginalPartialHomomorphismEmbedding A B f := by
  refine ⟨⟨hf.1.1, ?_⟩, hf.2⟩
  intro F x hnonempty
  exact hf.map_func_of_nonempty F x hnonempty

/-- Conversely, a 2019-style partial homomorphism-embedding
automatically satisfies the precise EHN weak interface used throughout
our verified native function construction. -/
theorem IsOriginalPartialHomomorphismEmbedding.toEHN
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : IsOriginalPartialHomomorphismEmbedding A B f) :
    A.IsEHNHomomorphismEmbedding B f :=
  ⟨hf.1.toWeak, hf.2⟩

/-- **Exact semantic equivalence:** EHN weak projections as encoded in
our Lean development are precisely original-style partial
homomorphism-embeddings when undefined inputs are represented by
empty fibres and defined inputs have nonempty values. -/
theorem originalPartialHE_iff_EHN
    {A : Structure L U} {B : Structure L V} {f : U → V} :
    IsOriginalPartialHomomorphismEmbedding A B f ↔
      A.IsEHNHomomorphismEmbedding B f := by
  constructor
  · exact IsOriginalPartialHomomorphismEmbedding.toEHN
  · exact IsEHNHomomorphismEmbedding.toOriginalPartial

/-- Full embeddings in the present `Structure` representation reflect
function-domain definedness, just as embeddings do in 2019. -/
theorem Embedding.originalPartialDomain_iff
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → U) :
    InOriginalPartialDomain B F (e ∘ x) ↔
      InOriginalPartialDomain A F x := by
  change (B.func F (e ∘ x)).Nonempty ↔ (A.func F x).Nonempty
  rw [← e.map_func F x]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := hy
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨e z, ⟨z, hz, rfl⟩⟩

/-- A strict *full-functional* B-tree target with a map which is
a homomorphism-embedding in the original 2019 partial-function sense.
This is deliberately weaker than the later total-fibre
`HasTreeCompletion`, even though the target tree and its gluing maps
are still strict, genuine full-functional objects. -/
def HasOriginalPartialTreeCompletion
    (Base : Structure L V) (A : Structure L U) : Prop :=
  ∃ (W : Type v) (T : Structure L W),
    TreeAmalgam Base W T ∧
    ∃ f : U → W, IsOriginalPartialHomomorphismEmbedding A T f

/-- An EHN map directly into B gives a one-copy strict functional
B-tree completion in the original partial-function semantics.
An undefined source function fibre may map to a defined B-fibre. -/
theorem HasOriginalPartialTreeCompletion.ofEHN_to_base
    (Base : Structure L V) (A : Structure L U)
    (f : U → V) (hf : A.IsEHNHomomorphismEmbedding Base f) :
    HasOriginalPartialTreeCompletion Base A := by
  exact ⟨V, Base,
    TreeAmalgam.copy (Embedding.id Base) (fun b => ⟨b, rfl⟩),
    f, hf.toOriginalPartial⟩

end StructuralRamsey.Structure
