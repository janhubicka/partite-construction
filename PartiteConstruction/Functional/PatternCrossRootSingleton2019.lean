import PartiteConstruction.Functional.PatternDecodedInducedMap2019
import PartiteConstruction.Functional.PatternDecodedOutputHull2019
import PartiteConstruction.Functional.PatternDomainCoherence2019

/-!
# Cross-pattern uniqueness of decoded positive-arity partial functions

The final U-closed tagged Picture may have different OLD equality
pattern representations of ONE original argument tuple. Their
root sizes and enumerations can differ syntactically, and the fresh
closure rules are distinct, so fixed-root uniqueness alone does not
compare their outputs.

Every decoded output lies in the U-hull H of the EXACT original
argument vertices, independent of its equality pattern. An active
OLD domain tuple makes H U-irreducible, and final B-copy coverage
embeds H FULLY into canonical tagged singleton-valued Base.

Under this one full embedding, the old output graph tuples of ALL
patterns decode to outputs of the SAME primitive Base function on
the SAME image of the original arguments. Singleton-valuedness of
Base then forces equality, reflected by embedding injectivity.

This proves the core positive-arity noncanonical-decoding condition
without assuming global canonicality or inflating weak source tests.
Nullary symbols still use the independent fixed-root reduction.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Two decoded OLD outputs of the same positive-arity primitive
function input coincide under a U-closed normal final Picture and
protected coverage by canonical singleton-valued Base, even when
the two outputs use DIFFERENT equality-pattern presentations. -/
theorem PatternTagNormal.decoded_output_unique_of_covered
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hBaseSingleton : Base.SingletonValued)
    (hC : IsUClosed L.patternClosureRules C)
    (hNormal : PatternTagNormal C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph)))
    (F : L.FuncSymbol) (hArity : 0 < L.funcArity F)
    (x : Fin (L.funcArity F) → V)
    (y z : V)
    (hy : y ∈
      (Structure.patternDecode (patternTagReduct C)).func F x)
    (hz : z ∈
      (Structure.patternDecode (patternTagReduct C)).func F x) :
    y = z := by
  classical
  obtain ⟨m, r, hr, root, hinj, hFact, hDom, hGraph⟩ := hy
  let p : Language.FunctionInputPattern L := {
    symbol := F
    rootSize := m
    argMap := r
    onto := hr
  }
  have hHy : y ∈
      (Structure.patternDecode (patternTagReduct C)).func F x :=
    ⟨m, r, hr, root, hinj, hFact, hDom, hGraph⟩
  let S : Set V := Set.range root
  let H : Set V := UClosureHull L.patternClosureRules C S
  have hRange : S = Set.range x :=
    equalityPattern_range_eq x r hr root hFact
  have hInput (i : Fin (L.funcArity F)) : x i ∈ H := by
    have hi : root (r i) ∈ H :=
      subset_UClosureHull L.patternClosureRules C S
        ⟨r i, rfl⟩
    rw [hFact i]
    exact hi
  have hyH : y ∈ H := by
    have h := hNormal.decoded_output_mem_inputHull
      C F hArity x y hHy
    rw [← hRange] at h
    exact h
  have hzH : z ∈ H := by
    have h := hNormal.decoded_output_mem_inputHull
      C F hArity x z hz
    rw [← hRange] at h
    exact h
  obtain ⟨g⟩ :=
    patternTag_domainHull_embeds_canonical_base
      C Base hC hCover p root hDom
  let xH : Fin (L.funcArity F) → H :=
    fun i => ⟨x i, hInput i⟩
  let yH : H := ⟨y, hyH⟩
  let zH : H := ⟨z, hzH⟩
  have hyB : g yH ∈ Base.func F (g ∘ xH) :=
    g.map_patternDecode_of_induced_tag_embedding
      H F x hInput y hyH hHy
  have hzB : g zH ∈ Base.func F (g ∘ xH) :=
    g.map_patternDecode_of_induced_tag_embedding
      H F x hInput z hzH hz
  have heq : g yH = g zH :=
    hBaseSingleton F (g ∘ xH) (g yH) (g zH) hyB hzB
  have heqH : yH = zH := g.injective heq
  exact congrArg Subtype.val heqH

end StructuralRamsey.RelStructure
