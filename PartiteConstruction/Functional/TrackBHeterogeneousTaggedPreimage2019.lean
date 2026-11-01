import PartiteConstruction.Functional.NativeTaggedWeakPreimage

/-!
# Track B: heterogeneous-universe full tagged weak-preimage embeddings

The canonical 2019 pattern graph of a FULL native embedding preserves
all relation tuples, exact function-output fibres and complete input
equality patterns on the literal original vertex map.

Earlier `Embedding.patternGraph` and `taggedPatternWeakPreimage`
were instantiated for carriers in ONE Lean universe. Genuine native
Hales--Jewett powers have carrier `Induced.Vertex B N`, whose universe
is the maximum of the input-part universe and the original vertex
universe. Its source B may live in a smaller universe.

This file generalizes ONLY the source-map API to different carrier
universes, without changing a structure, inserting a vertex, or
making arbitrary weak tests into closed/full functional subobjects.
-/

namespace StructuralRamsey.Structure.Embedding

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {A : Structure L V} {B : Structure L W}

/-- A FULL native functional embedding reflects and preserves all
equality-pattern OLD relations for possibly DIFFERENT source/target
carrier universes. Complete function-value fibres are reflected using
injectivity; empty-domain patterns are reflected as well. -/
def heteroPatternGraph (e : Embedding A B) :
    RelStructure.Embedding A.patternGraph B.patternGraph where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | P
    · exact e.map_rel_iff R xs
    · rcases P with pat | pat
      · let args : Fin (L.funcArity pat.symbol) → V :=
          xs ∘ pat.argMap
        have hInj : Function.Injective (e ∘ xs) ↔
            Function.Injective xs := by
          constructor
          · intro he i j hij
            exact he (congrArg e hij)
          · intro hx i j hij
            exact hx (e.injective hij)
        have hDom :
            (B.func pat.symbol (e ∘ args)).Nonempty ↔
              (A.func pat.symbol args).Nonempty := by
          constructor
          · rintro ⟨z, hz⟩
            rw [← e.map_func pat.symbol args] at hz
            obtain ⟨y, hy, _⟩ := hz
            exact ⟨y, hy⟩
          · rintro ⟨y, hy⟩
            refine ⟨e y, ?_⟩
            rw [← e.map_func pat.symbol args]
            exact ⟨y, hy, rfl⟩
        change
          (Function.Injective (e ∘ xs) ∧
            (B.func pat.symbol (e ∘ args)).Nonempty) ↔
          (Function.Injective xs ∧
            (A.func pat.symbol args).Nonempty)
        exact and_congr hInj hDom
      · let root : Fin pat.rootSize → V :=
          fun i => xs (Fin.castSucc i)
        let args : Fin (L.funcArity pat.symbol) → V :=
          root ∘ pat.argMap
        let output : V := xs (Fin.last pat.rootSize)
        have hInj : Function.Injective (e ∘ root) ↔
            Function.Injective root := by
          constructor
          · intro he i j hij
            exact he (congrArg e hij)
          · intro hx i j hij
            exact hx (e.injective hij)
        have hVal :
            e output ∈ B.func pat.symbol (e ∘ args) ↔
              output ∈ A.func pat.symbol args := by
          constructor
          · intro hy
            rw [← e.map_func pat.symbol args] at hy
            obtain ⟨z, hz, hzy⟩ := hy
            have hEq : z = output := e.injective hzy
            rwa [hEq] at hz
          · intro hy
            rw [← e.map_func pat.symbol args]
            exact ⟨output, hy, rfl⟩
        change
          (Function.Injective (e ∘ root) ∧
            e output ∈ B.func pat.symbol (e ∘ args)) ↔
          (Function.Injective root ∧
            output ∈ A.func pat.symbol args)
        exact and_congr hInj hVal

/-- The exact SAME original full native vertex map restricts to a FULL
canonical 2019 TAGGED relational embedding between ambient-induced
weak tests, even when the two vertex types have distinct universe
levels. Source vertices are exactly e⁻¹(S), target vertices exactly S;
every old domain bit, output relation and fresh complete U-root tag is
preserved and reflected without taking closure. -/
noncomputable def heteroTaggedPatternWeakPreimage
    (e : Embedding A B) (S : Set W) :
    RelStructure.Embedding
      ((patternTagExpansion A.patternGraph).induce (e.toFun ⁻¹' S))
      ((patternTagExpansion B.patternGraph).induce S) where
  toFun := fun x => ⟨e x.1, x.2⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro R xs
    change (patternTagExpansion B.patternGraph).rel R
        (e.toFun ∘ (Subtype.val ∘ xs)) ↔
      (patternTagExpansion A.patternGraph).rel R
        (Subtype.val ∘ xs)
    exact ((e.heteroPatternGraph).patternTag).map_rel_iff R
      (Subtype.val ∘ xs)

end StructuralRamsey.Structure.Embedding
