import PartiteConstruction.Functional.PatternGraphReconstruction2019
import PartiteConstruction.Functional.PatternDomainCompletion2019
import PartiteConstruction.Functional.PatternDomainCoherence2019
import PartiteConstruction.Functional.PatternTagCoverageLaws2019

/-!
# The OLD graph of a covered tagged Picture equals its canonical decode

The U-closed final Picture of the corrected 2019 construction need
not be globally canonical by construction. However, protected closed
B-copy coverage forces BOTH directions of all OLD domain and graph
relation symbols in terms of their primitive decoded functions.

For output graphs the nontrivial direction takes a decoded value
witnessed by ANY pattern and reflects the desired pattern's graph
from one fully embedded exact weak irreducible tuple support.

For domains the OLD active relation implies existence of a fresh
closure output (canonical closedness lemma), and the converse uses
graph reconstruction plus old graph-root validity. This requires
positive primitive function arities: nullary symbols are treated by
the separate common-root reduction.

Thus the entire OLD relational structure is pointwise EXACTLY the
canonical equality-pattern graph expansion of its native decoder,
without changing the vertex set or weakening full embeddings.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- On a U-closed Picture with protected coverage into canonical B,
every OLD equality-pattern relation coincides with the canonical
graph relation of the decoded native function structure. This is
the fundamental noncanonical-to-canonical bridge for positive arity. -/
theorem patternGraph_reconstruction_rel_iff
    (C : RelStructure (L.patternTag) V)
    (Base : Structure L W)
    (hPositive : ∀ F : L.FuncSymbol, 0 < L.funcArity F)
    (hC : IsUClosed L.patternClosureRules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure (L.patternTag) X),
      IsUClosed L.patternClosureRules Test →
      IsUIrreducible L.patternClosureRules Test →
      Embedding Test C →
      Nonempty (Embedding Test (patternTagExpansion Base.patternGraph))) :
    ∀ (R : (L.patternGraph).Symbol)
      (t : Fin ((L.patternGraph).arity R) → V),
      (Structure.patternDecode (patternTagReduct C)).patternGraph.rel R t ↔
        (patternTagReduct C).rel R t := by
  classical
  have hBaseNormal : PatternTagNormal
      (patternTagExpansion Base.patternGraph) :=
    patternTag_normal_canonical Base.patternGraph
  have hBaseValid : PatternTagGraphRootValid
      (patternTagExpansion Base.patternGraph) :=
    patternTag_valid_canonical Base
  obtain ⟨hNormal, hValid⟩ :=
    patternTag_local_laws_of_closed_coverage C
      (patternTagExpansion Base.patternGraph)
      hC hBaseNormal hBaseValid hCover
  intro R t
  rcases R with R | Q
  · exact Iff.rfl
  · rcases Q with p | p
    · -- OLD function-domain relation.
      constructor
      · intro ht
        change Function.Injective t ∧
          ((Structure.patternDecode (patternTagReduct C)).func
            p.symbol (t ∘ p.argMap)).Nonempty at ht
        obtain ⟨hinj, y, hy⟩ := ht
        have hGraph :=
          patternGraph_output_of_decoded_covered
            C Base hC hCover p t hinj y hy
        have hd := hValid p (Structure.funcTuple t y) hGraph
        simpa only [Structure.funcTuple_castSucc] using hd
      · intro hd
        have hinj : Function.Injective t :=
          patternTag_domain_injective_of_canonical_coverage
            C Base hC hCover p t hd
        have hpos : 0 < p.rootSize := by
          rcases Nat.eq_zero_or_pos p.rootSize with hZero | hPos
          · have i : Fin (L.funcArity p.symbol) :=
              ⟨0, hPositive p.symbol⟩
            have z : Fin 0 := hZero ▸ p.argMap i
            exact Fin.elim0 z
          · exact hPos
        obtain ⟨y, hyGraph⟩ :=
          hNormal.old_domain_has_output C hC p hpos t hinj hd
        have hy : y ∈
            (Structure.patternDecode (patternTagReduct C)).func
              p.symbol (t ∘ p.argMap) :=
          ⟨p.rootSize, p.argMap, p.onto, t, hinj,
            (fun _ => rfl), hd, hyGraph⟩
        exact ⟨hinj, ⟨y, hy⟩⟩
    · -- OLD function-output graph relation.
      let root : Fin p.rootSize → V :=
        fun i => t i.castSucc
      let y : V := t (Fin.last p.rootSize)
      have hTuple : t = Structure.funcTuple root y := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [root, y, Structure.funcTuple_last]
        · simp only [root, y, Structure.funcTuple_castSucc]
      constructor
      · intro ht
        change Function.Injective root ∧
          y ∈ (Structure.patternDecode (patternTagReduct C)).func
            p.symbol (root ∘ p.argMap) at ht
        have hOld :=
          patternGraph_output_of_decoded_covered
            C Base hC hCover p root ht.1 y ht.2
        rw [← hTuple] at hOld
        exact hOld
      · intro ht
        have hd :
            (patternTagReduct C).rel (.inr (.inl p)) root := by
          have h := hValid p t ht
          simpa only [root] using h
        have hinj : Function.Injective root :=
          patternTag_domain_injective_of_canonical_coverage
            C Base hC hCover p root hd
        have hGraphTuple :
            (patternTagReduct C).rel (.inr (.inr p))
              (Structure.funcTuple root y) := by
          rw [← hTuple]
          exact ht
        have hy : y ∈
            (Structure.patternDecode (patternTagReduct C)).func
              p.symbol (root ∘ p.argMap) :=
          ⟨p.rootSize, p.argMap, p.onto, root, hinj,
            (fun _ => rfl), hd, hGraphTuple⟩
        exact ⟨hinj, hy⟩

end StructuralRamsey.RelStructure
