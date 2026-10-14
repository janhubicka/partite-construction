import PartiteConstruction.Functional.PartialFunctionPatternDecode2019

/-!
# Reflect a genuine singleton-valued function embedding from pattern graphs

The equality-pattern relational representation records domain incidence
as well as every output tuple, for arbitrary repeated function inputs.

For a *singleton-valued target*, a full relational embedding of canonical
pattern graphs reflects the existence of each function fibre, and the
preservation of one realized source output determines the entire target
fibre. Thus the SAME underlying vertex map is a genuine full function
embedding, without changing any source vertices.

This is independent of the stronger EHN projection notion; it is the
full-embedding half of the faithful 2019 partial-function translation.
-/

namespace StructuralRamsey.Structure.Embedding

open StructuralRamsey

universe u v
variable {L : Language.{u}}
variable {V W : Type v}
variable {A : Structure L V} {B : Structure L W}

/-- A full induced embedding of canonical domain-and-output pattern
graphs into a SINGLETON-VALUED target yields an actual full embedding
of the original partial-function structures on the same vertex map. -/
def ofPatternGraph [Finite V]
    (hB : B.SingletonValued)
    (e : RelStructure.Embedding A.patternGraph B.patternGraph) :
    Embedding A B where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R x
    exact e.map_rel_iff (.inl R) x
  map_func := by
    classical
    intro F x
    obtain ⟨m, r, root, hr, hinj, hfact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact x
    let pat : Language.FunctionInputPattern L := {
      symbol := F
      rootSize := m
      argMap := r
      onto := hr
    }
    have hInput : root ∘ r = x := by
      funext i
      exact (hfact i).symm
    have hInputTarget : (e ∘ root) ∘ r = e ∘ x := by
      funext i
      exact congrArg e (hfact i).symm
    have hOutput (z : V) (hz : z ∈ A.func F x) :
        e z ∈ B.func F (e ∘ x) := by
      have hGraphA : A.patternGraph.rel (.inr (.inr pat))
          (Structure.funcTuple root z) := by
        change Function.Injective root ∧ z ∈ A.func F (root ∘ r)
        refine ⟨hinj, ?_⟩
        rw [hInput]
        exact hz
      have hGraphB :=
        (e.map_rel_iff (.inr (.inr pat))
          (Structure.funcTuple root z)).mpr hGraphA
      have hComp := Structure.comp_funcTuple e root z
      rw [hComp] at hGraphB
      change Function.Injective (e ∘ root) ∧
        e z ∈ B.func F ((e ∘ root) ∘ r) at hGraphB
      rw [hInputTarget] at hGraphB
      exact hGraphB.2
    have hDefined (hTarget : (B.func F (e ∘ x)).Nonempty) :
        (A.func F x).Nonempty := by
      have hDomB : B.patternGraph.rel (.inr (.inl pat))
          (e ∘ root) := by
        change Function.Injective (e ∘ root) ∧
          (B.func F ((e ∘ root) ∘ r)).Nonempty
        refine ⟨e.injective.comp hinj, ?_⟩
        rw [hInputTarget]
        exact hTarget
      have hDomA :=
        (e.map_rel_iff (.inr (.inl pat)) root).mp hDomB
      change Function.Injective root ∧
        (A.func F (root ∘ r)).Nonempty at hDomA
      rw [hInput] at hDomA
      exact hDomA.2
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hOutput z hz
    · intro hy
      obtain ⟨z, hz⟩ := hDefined ⟨y, hy⟩
      have hyz : y = e z :=
        hB F (e ∘ x) y (e z) hy (hOutput z hz)
      exact ⟨z, hz, hyz.symm⟩

/-- On finite sources and singleton-valued targets, the canonical
equality-pattern graph representation preserves and REFLECTS full
embeddings. This is an equivalence with the *same* underlying map,
not a quotient or an extension by closure vertices. -/
def patternGraphEquiv [Finite V] (hB : B.SingletonValued) :
    Embedding A B ≃
      RelStructure.Embedding A.patternGraph B.patternGraph where
  toFun := patternGraph
  invFun := ofPatternGraph hB
  left_inv := by
    intro f
    apply Embedding.ext
    intro x
    rfl
  right_inv := by
    intro f
    apply RelStructure.Embedding.ext
    intro x
    rfl

end StructuralRamsey.Structure.Embedding
