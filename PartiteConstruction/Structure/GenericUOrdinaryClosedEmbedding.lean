import PartiteConstruction.Structure.GenericUGraphSemantics
import PartiteConstruction.Structure.GenericUGraphInverse
import PartiteConstruction.Structure.GenericUGraphPartiteInverse
import PartiteConstruction.Structure.GenericUCombinedClosureBridge
import PartiteConstruction.Functional.Closed

/-!
# Track F — ordinary (non-partite) U-closed embeddings for Picture data

In the survey's induced Picture lemma the distinguished alpha:A→D is
an ORIGINAL induced relational embedding with U-closed image, not a
partite embedding. The verified graph Picture lemma requires a closed
graph embedding. These must be compared on the literal same injection.

Every relation outside U is retained, each relation in U is replaced
by its set-valued function graph with the same last-coordinate incidence,
and no coherence condition or extra vertices are introduced.
-/

namespace StructuralRamsey
universe u v w

namespace RelStructure

variable {L : RelLanguage.{u}} {V : Type v} {W : Type w}

/-- The genuine graph relation for every designated last output agrees
with the corresponding original relation tuple for any relational A. -/
theorem reducedUGraph_func_snoc_iff
    (A : RelStructure L V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (F : U) (x : Fin (L.arity F.1 - 1) → V) (y : V) :
    (A.asReducedUGraph U hU).rel (.inr F)
      (Structure.funcTuple x y) ↔
      A.rel F.1 (RelLanguage.appendU L U hU F x y) := by
  calc
    (A.asReducedUGraph U hU).rel (.inr F)
        (Structure.funcTuple x y) ↔
      (A.asUFunctionsReduced U hU).graph.rel (.inr F)
        (Structure.funcTuple x y) :=
      A.asReducedUGraph_iff_functionGraph U hU (.inr F) _
    _ ↔ y ∈ (A.asUFunctionsReduced U hU).func F x :=
      Structure.graph_func_snoc (A.asUFunctionsReduced U hU) F x y
    _ ↔ A.rel F.1 (RelLanguage.appendU L U hU F x y) := Iff.rfl

namespace Embedding

variable {A : RelStructure L V} {B : RelStructure L W}

/-- An arbitrary induced embedding between canonical reindexed structures
recovers the ORIGINAL full induced relation embedding on the same map. -/
noncomputable def ofReducedReindex
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (g : Embedding (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU)) : Embedding A B where
  toFun := g
  injective := g.injective
  map_rel_iff := by
    intro R t
    let ef := RelStructure.Embedding.fromReducedUGraph U hU g
    calc
      B.rel R (g.toFun ∘ t) ↔
        (RelStructure.fromReducedUGraph U hU
          (B.asReducedUGraph U hU)).rel R
          (g.toFun ∘ t) :=
        (B.from_asReducedUGraph_rel_iff U hU R (g.toFun ∘ t)).symm
      _ ↔ (RelStructure.fromReducedUGraph U hU
          (A.asReducedUGraph U hU)).rel R t :=
        ef.map_rel_iff R t
      _ ↔ A.rel R t :=
        A.from_asReducedUGraph_rel_iff U hU R t

/-- Original U-closed induced embeddings become fully closed function
graph embeddings, retaining precisely the original vertex injection. -/
noncomputable def toReducedGraphClosed
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : Embedding A B)
    (he : IsUClosedEmbeddingRange U hU e) :
    ClosedEmbedding (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU) where
  toEmbedding := e.asReducedUGraph U hU
  closed := by
    have hlift : IsUClosedEmbedding A B U hU e :=
      (isUClosedEmbedding_iff_range U hU e).mpr he
    intro F x y hy
    have hrel : B.rel F.1
        (RelLanguage.appendU L U hU F (e.toFun ∘ x) y) :=
      (B.reducedUGraph_func_snoc_iff U hU F
        (e.toFun ∘ x) y).mp hy
    obtain ⟨z, hz, hez⟩ := hlift F x y hrel
    exact ⟨z, (A.reducedUGraph_func_snoc_iff U hU F x z).mpr hz, hez⟩

/-- A fully closed graph embedding between the two exact original
encodings decodes to the original U-closed relational embedding subtype. -/
noncomputable def fromReducedGraphClosed
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (e : ClosedEmbedding (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU)) :
    {f : Embedding A B // IsUClosedEmbeddingRange U hU f} := by
  let f := ofReducedReindex U hU e.toEmbedding
  have hclosed : IsUClosedEmbedding A B U hU f := by
    intro F x y hy
    have hyG : (B.asReducedUGraph U hU).rel (.inr F)
        (Structure.funcTuple (f.toFun ∘ x) y) :=
      (B.reducedUGraph_func_snoc_iff U hU F
        (f.toFun ∘ x) y).mpr hy
    obtain ⟨z, hz, hzy⟩ := e.closed F x y hyG
    exact ⟨z, (A.reducedUGraph_func_snoc_iff U hU F x z).mp hz, hzy⟩
  exact ⟨f, (isUClosedEmbedding_iff_range U hU f).mp hclosed⟩

/-- Full embedding-TYPE equivalence for the distinguished alpha of the
Picture lemma, without adding a dummy partite partition or new language. -/
noncomputable def uClosedReducedGraphEquiv
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    {f : Embedding A B // IsUClosedEmbeddingRange U hU f} ≃
      ClosedEmbedding (A.asReducedUGraph U hU)
        (B.asReducedUGraph U hU) where
  toFun f := toReducedGraphClosed U hU f.1 f.2
  invFun e := fromReducedGraphClosed U hU e
  left_inv := by
    intro f
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply ClosedEmbedding.ext
    intro x
    rfl

end Embedding
end RelStructure
end StructuralRamsey
