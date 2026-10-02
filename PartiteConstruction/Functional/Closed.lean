import PartiteConstruction.Structure.Relationalize
import PartiteConstruction.Partite.Basic

/-! # Closed embeddings for relational encodings of set-valued functions

A function symbol of arity n is represented by an (n+1)-ary graph relation.
A relational embedding is closed when every graph-relation output over an
image input tuple is itself in the image.  Closed relational embeddings are
exactly full embeddings of the reconstructed set-valued-function structures.
-/
namespace StructuralRamsey

open Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type v} {W : Type w}

namespace RelStructure

/-- Every original function symbol has positive arity. Under graph encoding
this says every distinguished output relation has arity at least two. -/
def Language.PositiveFuncArity (L : Language.{u}) : Prop :=
  ∀ F, 0 < L.funcArity F

/-- A subset is closed for the encoded function-output relations. -/
def FunctionClosedSet
    (A : RelStructure L.graph V) (S : Set V) : Prop :=
  ∀ F (x : Fin (L.funcArity F) → V) y,
    A.rel (.inr F) (Structure.funcTuple x y) →
    (∀ i, x i ∈ S) → y ∈ S

/-- Closedness of a map for the function-graph relations. -/
def FunctionClosedMap
    (A : RelStructure L.graph V) (B : RelStructure L.graph W)
    (f : V → W) : Prop :=
  ∀ F (x : Fin (L.funcArity F) → V) y,
    B.rel (.inr F) (Structure.funcTuple (f ∘ x) y) →
    ∃ z, A.rel (.inr F) (Structure.funcTuple x z) ∧ f z = y

namespace FunctionClosedMap

variable {A : RelStructure L.graph V} {B : RelStructure L.graph W}
variable {X : Type*} {C : RelStructure L.graph X}
variable {f : V → W} {g : W → X}

theorem comp
    (hg : FunctionClosedMap B C g)
    (hf : FunctionClosedMap A B f) :
    FunctionClosedMap A C (g ∘ f) := by
  intro F x y hy
  have hy' :
      C.rel (.inr F)
        (Structure.funcTuple (g ∘ (f ∘ x)) y) := by
    have htuple :
        Structure.funcTuple (g ∘ (f ∘ x)) y =
          Structure.funcTuple ((g ∘ f) ∘ x) y := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Structure.funcTuple]
      · rfl
    rw [htuple]
    exact hy
  obtain ⟨b, hb, hby⟩ := hg F (f ∘ x) y hy'
  obtain ⟨a, ha, hab⟩ := hf F x b hb
  refine ⟨a, ha, ?_⟩
  change g (f a) = y
  rw [hab, hby]

end FunctionClosedMap

/-- A relational embedding closed for all encoded function outputs. -/
structure ClosedEmbedding
    (A : RelStructure L.graph V) (B : RelStructure L.graph W)
    extends Embedding A B where
  closed : FunctionClosedMap A B toFun

instance {A : RelStructure L.graph V} {B : RelStructure L.graph W} :
    CoeFun (ClosedEmbedding A B) (fun _ => V → W) :=
  ⟨fun e => e.toEmbedding⟩

namespace ClosedEmbedding

variable {A : RelStructure L.graph V} {B : RelStructure L.graph W}

@[ext] theorem ext {f g : ClosedEmbedding A B}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  simp only [ClosedEmbedding.mk.injEq]
  exact RelStructure.Embedding.ext h

/-- Inclusion of a function-closed subset is a closed relational embedding. -/
def inclusion
    (A : RelStructure L.graph V) (S : Set V)
    (hS : FunctionClosedSet A S) :
    ClosedEmbedding (A.induce S) A where
  toEmbedding := RelStructure.inclusion A S
  closed := by
    intro F x y hy
    have hxS : ∀ i, (x i).1 ∈ S := fun i => (x i).2
    have hyS : y ∈ S := hS F (Subtype.val ∘ x) y hy hxS
    refine ⟨⟨y, hyS⟩, ?_, rfl⟩
    change
      A.rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x ⟨y, hyS⟩)
    have htuple :
        Subtype.val ∘ Structure.funcTuple x ⟨y, hyS⟩ =
          Structure.funcTuple (Subtype.val ∘ x) y := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Structure.funcTuple, Function.comp_apply]
      · simp [Structure.funcTuple, Function.comp_apply]
    rw [htuple]
    exact hy


def id (A : RelStructure L.graph V) : ClosedEmbedding A A where
  toEmbedding := Embedding.id A
  closed := by
    intro F x y hy
    exact ⟨y, hy, rfl⟩

def comp {X : Type*} {C : RelStructure L.graph X}
    (g : ClosedEmbedding B C) (f : ClosedEmbedding A B) :
    ClosedEmbedding A C where
  toEmbedding := g.toEmbedding.comp f.toEmbedding
  closed := g.closed.comp f.closed

end ClosedEmbedding

end RelStructure

namespace Structure.Embedding

variable {A : Structure L V} {B : Structure L W}

/-- A full embedding becomes a closed embedding of relational graphs. -/
def toClosedGraph (e : Structure.Embedding A B) :
    RelStructure.ClosedEmbedding A.graph B.graph where
  toEmbedding := e.graph
  closed := by
    intro F x y hy
    have hyFull : y ∈ B.func F (e ∘ x) := by
      exact (Structure.graph_func_snoc B F (e ∘ x) y).mp hy
    rw [← e.map_func F x] at hyFull
    rcases hyFull with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    exact (Structure.graph_func_snoc A F x z).2 hz

end Structure.Embedding

namespace RelStructure.ClosedEmbedding

variable {A : RelStructure L.graph V} {B : RelStructure L.graph W}

/-- A closed relational graph embedding reconstructs a full embedding of the
associated set-valued-function structures. -/
def toFull (e : ClosedEmbedding A B) :
    Structure.Embedding (Structure.ofGraph A) (Structure.ofGraph B) where
  toFun := e
  injective := e.toEmbedding.injective
  map_rel_iff := by
    intro R x
    exact e.toEmbedding.map_rel_iff (.inl R) x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hs :
          A.rel (.inr F) (Structure.funcTuple x z) := hz
      have ht :=
        (e.toEmbedding.map_rel_iff (.inr F)
          (Structure.funcTuple x z)).mpr hs
      change
        B.rel (.inr F)
          (Structure.funcTuple (e ∘ x) (e z))
      have htuple :
          Structure.funcTuple (e ∘ x) (e z) =
            e ∘ Structure.funcTuple x z := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Structure.funcTuple]
        · simp [Structure.funcTuple, Function.comp_apply]
      rw [htuple]
      exact ht
    · intro hy
      have ht :
          B.rel (.inr F) (Structure.funcTuple (e ∘ x) y) := hy
      obtain ⟨z, hz, hzy⟩ := e.closed F x y ht
      exact ⟨z, hz, hzy⟩

end RelStructure.ClosedEmbedding

namespace Structure

variable {A : Structure L V} {B : Structure L W}

/-- A closed embedding from the graph of a full source into an arbitrary graph
structure reconstructs a full embedding into the structure decoded from that
target. -/
def Embedding.ofClosedGraphTarget
    {R : RelStructure L.graph W}
    (e : RelStructure.ClosedEmbedding A.graph R) :
    Structure.Embedding A (Structure.ofGraph R) where
  toFun := e
  injective := e.toEmbedding.injective
  map_rel_iff := by
    intro S x
    exact e.toEmbedding.map_rel_iff (.inl S) x
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hs :
          A.graph.rel (.inr F) (Structure.funcTuple x z) :=
        (Structure.graph_func_snoc A F x z).2 hz
      have ht :=
        (e.toEmbedding.map_rel_iff (.inr F)
          (Structure.funcTuple x z)).mpr hs
      have htuple :
          e ∘ Structure.funcTuple x z =
            Structure.funcTuple (e ∘ x) (e z) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Structure.funcTuple, Function.comp_apply]
        · simp [Structure.funcTuple, Function.comp_apply]
      rw [htuple] at ht
      exact ht
    · intro hy
      have ht :
          R.rel (.inr F) (Structure.funcTuple (e ∘ x) y) := hy
      obtain ⟨z, hz, hzy⟩ := e.closed F x y ht
      have hzFull : z ∈ A.func F x :=
        (Structure.graph_func_snoc A F x z).1 hz
      exact ⟨z, hzFull, hzy⟩

/-- Recover a full embedding directly from a closed embedding of the graph
encodings. -/
def Embedding.ofClosedGraph
    (e : RelStructure.ClosedEmbedding A.graph B.graph) :
    Structure.Embedding A B := by
  apply Structure.Embedding.ofGraphClosed e.toEmbedding
  intro F x y hy
  have ht :
      B.graph.rel (.inr F)
        (Structure.funcTuple (e ∘ x) y) :=
    (Structure.graph_func_snoc B F (e ∘ x) y).2 hy
  obtain ⟨z, hz, hzy⟩ := e.closed F x y ht
  refine ⟨z, ?_, hzy⟩
  exact (Structure.graph_func_snoc A F x z).1 hz

/-- Full embeddings are equivalent to U-closed graph embeddings. -/
def embeddingEquivClosedGraph :
    Structure.Embedding A B ≃
      RelStructure.ClosedEmbedding A.graph B.graph where
  toFun := Structure.Embedding.toClosedGraph
  invFun := Structure.Embedding.ofClosedGraph
  left_inv := by
    intro e
    apply Structure.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.ClosedEmbedding.ext
    intro x
    rfl

end Structure

namespace RelStructure

/-- Ramsey arrow using only U-closed embeddings. -/
def ClosedArrow
    (A : RelStructure L.graph V)
    (B : RelStructure L.graph W)
    {X : Type*} (C : RelStructure L.graph X)
    (κ : Type*) : Prop :=
  ∀ χ : ClosedEmbedding A C → κ,
    ∃ f : ClosedEmbedding B C,
      ∀ e₁ e₂ : ClosedEmbedding A B,
        χ (f.comp e₁) = χ (f.comp e₂)

end RelStructure

namespace Structure

variable {A : Structure L V} {B : Structure L W}

/-- The full structural Ramsey arrow is exactly the closed-arrow statement for
the relational graph encodings. -/
theorem arrow_iff_closedGraph
    {X : Type*} (C : Structure L X) (κ : Type*) :
    Structure.Arrow A B C κ ↔
      RelStructure.ClosedArrow A.graph B.graph C.graph κ := by
  constructor
  · intro h χ
    let χfull : Structure.Embedding A C → κ :=
      fun e => χ (Structure.Embedding.toClosedGraph e)
    obtain ⟨f, hf⟩ := h χfull
    refine ⟨Structure.Embedding.toClosedGraph f, ?_⟩
    intro e₁ e₂
    let e₁f := Structure.Embedding.ofClosedGraph e₁
    let e₂f := Structure.Embedding.ofClosedGraph e₂
    have hh := hf e₁f e₂f
    simpa [χfull, e₁f, e₂f] using hh
  · intro h χ
    let χgraph :
        RelStructure.ClosedEmbedding A.graph C.graph → κ :=
      fun e => χ (Structure.Embedding.ofClosedGraph e)
    obtain ⟨f, hf⟩ := h χgraph
    refine ⟨Structure.Embedding.ofClosedGraph f, ?_⟩
    intro e₁ e₂
    have hh := hf
      (Structure.Embedding.toClosedGraph e₁)
      (Structure.Embedding.toClosedGraph e₂)
    simpa [χgraph] using hh

end Structure

namespace Partite

/-- U-transversality for the encoded function graph relations: all outputs
of one function application occupy distinct parts. -/
def System.FunctionOutputTransversal
    (B : System L.graph P V) : Prop :=
  ∀ F (x : Fin (L.funcArity F) → V) y z,
    B.rel (.inr F) (Structure.funcTuple x y) →
    B.rel (.inr F) (Structure.funcTuple x z) →
    B.part y = B.part z → y = z

/-- The source and output coordinates of every encoded function incidence are
already transversal because B is a partite system; this predicate is the
additional cross-output condition called U-transversality in the survey. -/
abbrev UTransversal := @System.FunctionOutputTransversal L P V

end Partite

end StructuralRamsey
