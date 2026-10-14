import PartiteConstruction.Functional.PatternGraphExactReconstruction2019
import PartiteConstruction.Functional.PatternTagIdentity2019

/-!
# Full identity embeddings between final tagged Picture and decoded natives

Under the positive-arity, U-closed and protected canonical B-cover
hypotheses, the OLD relational reduct of a final tagged Picture is
EXACTLY the canonical equality-pattern graph of its decoded native
function structure. Consequently, both old structures fully embed
into one another on the identity map.

The verified full-root tag normality of that same Picture lifts
these OLD embeddings to full embeddings between its complete tagged
structure and the canonical fresh-root-tag expansion of its decoded
native structure. This is stronger than a positive graph-homomorphism
transfer: ALL old and fresh relations are reflected, including
undefined primitive function domains.

The vertex carrier is unchanged throughout. Nullary functions
must be removed by the pre-existing common fixed-root reduction
before applying the positive-arity theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Full OLD graph embedding from the noncanonical final Picture into
the canonical graph of its decoded native primitive functions. -/
def patternGraph_to_decodedEmbedding
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hPositive : ∀ F : L.FuncSymbol, 0 < L.funcArity F)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph))) :
    Embedding (patternTagReduct C)
      (Structure.patternDecode (patternTagReduct C)).patternGraph where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    simpa only [Function.id_comp] using
      (patternGraph_reconstruction_rel_iff
        C Base hPositive hC hCover R xs)

/-- Conversely, the canonical OLD graph of the decoded native
function structure fully embeds into the actual OLD Picture. -/
def patternGraph_from_decodedEmbedding
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hPositive : ∀ F : L.FuncSymbol, 0 < L.funcArity F)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph))) :
    Embedding (Structure.patternDecode (patternTagReduct C)).patternGraph
      (patternTagReduct C) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := by
    intro R xs
    simpa only [Function.id_comp] using
      (patternGraph_reconstruction_rel_iff
        C Base hPositive hC hCover R xs).symm

/-- The entire final tagged Picture embeds FULLY, on the original
vertices, into the canonical tagged expansion of its decoded
primitive-function structure. -/
noncomputable def patternTag_to_decodedEmbedding
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hPositive : ∀ F : L.FuncSymbol, 0 < L.funcArity F)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph))) :
    Embedding C
      (patternTagExpansion
        (Structure.patternDecode (patternTagReduct C)).patternGraph) := by
  have hNormal : PatternTagNormal C :=
    (patternTag_local_laws_of_closed_coverage C
      (patternTagExpansion Base.patternGraph)
      hC (patternTag_normal_canonical Base.patternGraph)
      (patternTag_valid_canonical Base) hCover).1
  exact (Embedding.patternTag
    (patternGraph_to_decodedEmbedding
      C Base hPositive hC hCover)).comp
    hNormal.toCanonicalEmbedding

/-- The reverse FULL tagged embedding also uses the original vertex
identity: the entire fresh closure-root representation is faithful
for each noncanonical final Picture under protected B-cover. -/
noncomputable def patternTag_from_decodedEmbedding
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hPositive : ∀ F : L.FuncSymbol, 0 < L.funcArity F)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph))) :
    Embedding
      (patternTagExpansion
        (Structure.patternDecode (patternTagReduct C)).patternGraph) C := by
  have hNormal : PatternTagNormal C :=
    (patternTag_local_laws_of_closed_coverage C
      (patternTagExpansion Base.patternGraph)
      hC (patternTag_normal_canonical Base.patternGraph)
      (patternTag_valid_canonical Base) hCover).1
  exact hNormal.canonicalEmbedding.comp
    (Embedding.patternTag
      (patternGraph_from_decodedEmbedding
        C Base hPositive hC hCover))

end StructuralRamsey.RelStructure
