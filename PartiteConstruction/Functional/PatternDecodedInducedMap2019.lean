import PartiteConstruction.Functional.PatternDecodedPositiveMap2019
import PartiteConstruction.Functional.PatternTagLocalLaws2019

/-!
# Exact induced-source transport for decoded OLD function graph outputs

A decoded output of the whole OLD graph remains a decoded output of
an induced OLD graph on S, provided the original input vertices and
the output vertex all lie in S. Each equality-pattern witness has its
root values among those original input vertices because the repeated-
coordinate map is surjective.

Thus a FULL embedding of the tagged induced substructure into a
canonical function Base takes the decoded output to the SAME
primitive Base function input, with no extra closure vertices on
the source tuple. This is the reusable transfer needed for comparing
all outputs in one protected input hull.
-/

namespace StructuralRamsey.RelStructure.Embedding

open StructuralRamsey

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {C : RelStructure (L.patternTag) V}
variable {Base : Structure L W}

/-- Every output of the ambient OLD decoded function that lies in
an induced vertex set S survives as a decoded output of the exact
induced OLD structure, if all original arguments also lie in S. -/
theorem patternDecode_mem_induce
    (S : Set V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (hInput : ∀ i, x i ∈ S)
    (y : V) (hyS : y ∈ S)
    (hy : y ∈
      (Structure.patternDecode (RelStructure.patternTagReduct C)).func F x) :
    (⟨y, hyS⟩ : S) ∈
      (Structure.patternDecode
        (RelStructure.patternTagReduct (C.induce S))).func F
        (fun i => ⟨x i, hInput i⟩) := by
  obtain ⟨m, r, hr, root, hInj, hFact, hDom, hGraph⟩ := hy
  have hRoot (i : Fin m) : root i ∈ S := by
    obtain ⟨j, hj⟩ := hr i
    have heq : root i = x j := by
      calc
        root i = root (r j) := congrArg root hj.symm
        _ = x j := (hFact j).symm
    rw [heq]
    exact hInput j
  let rootS : Fin m → S := fun i => ⟨root i, hRoot i⟩
  let xS : Fin (L.funcArity F) → S :=
    fun i => ⟨x i, hInput i⟩
  let yS : S := ⟨y, hyS⟩
  have hInjS : Function.Injective rootS := by
    intro i j hij
    apply hInj
    exact congrArg Subtype.val hij
  have hFactS : ∀ i, xS i = rootS (r i) := by
    intro i
    apply Subtype.ext
    exact hFact i
  have hDomS :
      (RelStructure.patternTagReduct (C.induce S)).rel
        (.inr (.inl
          ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
            Language.FunctionInputPattern L))) rootS := by
    change C.rel (.inl (.inr (.inl
      ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
        Language.FunctionInputPattern L)))) (Subtype.val ∘ rootS)
    have hRootEq : Subtype.val ∘ rootS = root := rfl
    rw [hRootEq]
    exact hDom
  have hTuple :
      Subtype.val ∘ Structure.funcTuple rootS yS =
        Structure.funcTuple root y := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rfl
    · rfl
  have hGraphS :
      (RelStructure.patternTagReduct (C.induce S)).rel
        (.inr (.inr
          ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
            Language.FunctionInputPattern L)))
        (Structure.funcTuple rootS yS) := by
    change C.rel (.inl (.inr (.inr
      ({ symbol := F, rootSize := m, argMap := r, onto := hr } :
        Language.FunctionInputPattern L))))
      (Subtype.val ∘ Structure.funcTuple rootS yS)
    rw [hTuple]
    exact hGraph
  exact ⟨m, r, hr, rootS, hInjS, hFactS, hDomS, hGraphS⟩

/-- An arbitrary decoded output of the ambient OLD graph, restricted
to an induced source S containing its argument and output vertices,
maps into the primitive Base fibre under a FULL tagged embedding. -/
theorem map_patternDecode_of_induced_tag_embedding
    (S : Set V)
    (e : Embedding (C.induce S)
      (RelStructure.patternTagExpansion Base.patternGraph))
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (hInput : ∀ i, x i ∈ S)
    (y : V) (hyS : y ∈ S)
    (hy : y ∈
      (Structure.patternDecode (RelStructure.patternTagReduct C)).func F x) :
    e ⟨y, hyS⟩ ∈ Base.func F
      (e ∘ (fun i => (⟨x i, hInput i⟩ : S))) := by
  let eOld : Embedding
      (RelStructure.patternTagReduct (C.induce S))
      Base.patternGraph := e.patternTagReduct
  exact eOld.map_patternDecode_func F
    (fun i => (⟨x i, hInput i⟩ : S))
    ⟨y, hyS⟩
    (patternDecode_mem_induce S F x hInput y hyS hy)

end StructuralRamsey.RelStructure.Embedding
