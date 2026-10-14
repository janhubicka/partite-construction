import PartiteConstruction.Functional.PatternDecodedInducedMap2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Reconstruct every OLD output relation of an induced decoded function

A decoded function output may initially be witnessed by a DIFFERENT
equality-pattern relation from the one in which we want to express it.

The witness is an OLD graph tuple, so its exact vertex support is
ordinarily irreducible. Protected closed B-copy coverage embeds that
exact weak support FULLY into canonical tagged B. Decoded output
preservation under this induced embedding puts the output in the
corresponding primitive B function fibre. Therefore EVERY injective
root enumeration of the same original argument tuple produces its
canonical OLD output graph relation, by reflection through this one
full B-copy embedding.

This reconstructs output graph relations of a noncanonical final
Picture from its primitive decoded functions. It neither assumes
global canonicality nor requires a U-closure of the weak tuple
support. Existence/uniqueness of decoded fibres is proved separately.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- A decoded OLD primitive output belongs to the original OLD
output-graph relation for ANY alternative injective equality-pattern
presentation of the same arguments, provided the protected closed
U-irreducibles embed into a canonical tagged Base. -/
theorem patternGraph_output_of_decoded_covered
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph)))
    (p : Language.FunctionInputPattern L)
    (root : Fin p.rootSize → V)
    (hinj : Function.Injective root)
    (y : V)
    (hy : y ∈
      (Structure.patternDecode (patternTagReduct C)).func
        p.symbol (root ∘ p.argMap)) :
    (patternTagReduct C).rel (.inr (.inr p))
      (Structure.funcTuple root y) := by
  classical
  let x : Fin (L.funcArity p.symbol) → V := root ∘ p.argMap
  obtain ⟨m, r, hr, root0, hinj0, hFact, hDom0, hGraph0⟩ := hy
  let p0 : Language.FunctionInputPattern L := {
    symbol := p.symbol
    rootSize := m
    argMap := r
    onto := hr
  }
  let t0 : Fin (m + 1) → V := Structure.funcTuple root0 y
  let S : Set V := Set.range t0
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inr p0))) t0 hGraph0
  obtain ⟨g⟩ :=
    weak_irreducible_embeds_base_of_closed_coverage
      hC hCover S hIrred
  have hInput (i : Fin (L.funcArity p.symbol)) : x i ∈ S := by
    have h0 : root0 (r i) ∈ S := by
      refine ⟨Fin.castSucc (r i), ?_⟩
      simp only [S, t0, Structure.funcTuple_castSucc]
    exact (hFact i).symm ▸ h0
  have hyS : y ∈ S := by
    refine ⟨Fin.last m, ?_⟩
    simp only [S, t0, Structure.funcTuple_last]
  have hRoot (i : Fin p.rootSize) : root i ∈ S := by
    obtain ⟨j, hj⟩ := p.onto i
    have hEq : root i = x j := by
      calc
        root i = root (p.argMap j) := congrArg root hj.symm
        _ = x j := rfl
    rw [hEq]
    exact hInput j
  let rootS : Fin p.rootSize → S :=
    fun i => ⟨root i, hRoot i⟩
  let yS : S := ⟨y, hyS⟩
  let xS : Fin (L.funcArity p.symbol) → S :=
    fun i => ⟨x i, hInput i⟩
  have hInjS : Function.Injective rootS := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hDecoded :
      y ∈ (Structure.patternDecode (patternTagReduct C)).func
        p.symbol x :=
    ⟨m, r, hr, root0, hinj0, hFact, hDom0, hGraph0⟩
  have hValue : g yS ∈ Base.func p.symbol (g ∘ xS) :=
    g.map_patternDecode_of_induced_tag_embedding
      S p.symbol x hInput y hyS hDecoded
  have hArgs : g ∘ xS = (g ∘ rootS) ∘ p.argMap := by
    funext i
    rfl
  have hVal : g yS ∈
      Base.func p.symbol ((g ∘ rootS) ∘ p.argMap) := by
    rw [← hArgs]
    exact hValue
  have hTarget : Base.patternGraph.rel (.inr (.inr p))
      (Structure.funcTuple (g ∘ rootS) (g yS)) := by
    change Function.Injective
        (fun i : Fin p.rootSize =>
          (Structure.funcTuple (g ∘ rootS) (g yS)) i.castSucc) ∧
      (Structure.funcTuple (g ∘ rootS) (g yS))
        (Fin.last p.rootSize) ∈
        Base.func p.symbol
          ((fun i : Fin p.rootSize =>
            (Structure.funcTuple (g ∘ rootS) (g yS)) i.castSucc) ∘
              p.argMap)
    simpa only [Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using
      (show Function.Injective (g ∘ rootS) ∧
          g yS ∈ Base.func p.symbol
            ((g ∘ rootS) ∘ p.argMap) from
        ⟨g.injective.comp hInjS, hVal⟩)
  let gOld : Embedding (patternTagReduct (C.induce S))
      Base.patternGraph := g.patternTagReduct
  have hMapTuple :
      g ∘ Structure.funcTuple rootS yS =
        Structure.funcTuple (g ∘ rootS) (g yS) :=
    Structure.comp_funcTuple g rootS yS
  have hTarget' : Base.patternGraph.rel (.inr (.inr p))
      (gOld ∘ Structure.funcTuple rootS yS) :=
    hMapTuple.symm ▸ hTarget
  have hSource : (patternTagReduct (C.induce S)).rel
      (.inr (.inr p)) (Structure.funcTuple rootS yS) :=
    (gOld.map_rel_iff (.inr (.inr p))
      (Structure.funcTuple rootS yS)).mp hTarget'
  have hValTuple :
      Subtype.val ∘ Structure.funcTuple rootS yS =
        Structure.funcTuple root y := by
    calc
      Subtype.val ∘ Structure.funcTuple rootS yS =
          Structure.funcTuple (Subtype.val ∘ rootS)
            (Subtype.val yS) :=
        Structure.comp_funcTuple Subtype.val rootS yS
      _ = Structure.funcTuple root y := rfl
  have hSourceOld : C.rel (.inl (.inr (.inr p)))
      (Subtype.val ∘ Structure.funcTuple rootS yS) := hSource
  exact hValTuple ▸ hSourceOld

end StructuralRamsey.RelStructure
