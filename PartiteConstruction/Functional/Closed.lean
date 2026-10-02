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
    convert hy using 1
    funext i
    fin_cases i <;> rfl
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
      convert ht using 1
      funext i
      fin_cases i <;> rfl
    · intro hy
      have ht :
          B.rel (.inr F) (Structure.funcTuple (e ∘ x) y) := hy
      obtain ⟨z, hz, hzy⟩ := e.closed F x y ht
      exact ⟨z, hz, hzy⟩

end RelStructure.ClosedEmbedding

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
