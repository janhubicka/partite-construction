import PartiteConstruction.Functional.WholeMaskActiveRootExtraction
import PartiteConstruction.Functional.Closed

/-!
# The relative 2019 U-condition is exactly complete-mask tuple closure

A well-formed old complete-mask graph has valid domain activation
and injective DISTINCT input roots for every complete-value tuple.
In such a graph, the 2019 U-substructure condition for the full-root
tagged expansion is precisely closure under all complete-value tuples.

The statement holds for arbitrary OLD relational structures satisfying
the explicit local well-formedness predicate. In particular it applies
to exact induced weak carriers with persistent ambient domain masks,
without presupposing that the weak structure itself arose by recomputing
a function's operation domain.

This lemma separates the functional graph-to-U translation from
finite generator-rank bookkeeping and from target normality.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- Every complete-value tuple has an injective distinct-input root
and the corresponding active OLD domain-mask relation. -/
def HasValidCompleteMaskDomains
    (E : RelStructure (L.wholeMaskPatternLanguage P) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (t : Fin (p.rootSize + q.size) → V),
      E.rel (.inr (.inr (p,q))) t →
        Function.Injective (fun i : Fin p.rootSize =>
          t (Fin.castAdd q.size i)) ∧
        E.rel (.inr (.inl (p,q)))
          (fun i : Fin p.rootSize => t (Fin.castAdd q.size i))

/-- Relative closedness under complete whole-value relation tuples;
original relation symbols and defined-empty mask domains introduce
no new output vertices. -/
def IsClosedByWholeMaskTuples
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (Q : Set V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts P)
    (t : Fin (p.rootSize + q.size) → V),
      E.rel (.inr (.inr (p,q))) t →
      (∀ i : Fin p.rootSize, t (Fin.castAdd q.size i) ∈ Q) →
      ∀ j : Fin q.size, t (Fin.natAdd p.rootSize j) ∈ Q

/-- The canonical genuinely partial source has valid complete mask
domain incidence and distinct-input root injection. -/
theorem PartialSetStructure.wholeMaskPatternGraph_validDomains
    (A : PartialSetStructure L V) (part : V → P) :
    HasValidCompleteMaskDomains (A.wholeMaskPatternGraph part) := by
  intro p q t ht
  exact ⟨ht.1, A.wholeMaskPatternGraph_output_has_domain part p q t ht⟩

/-- Validity is hereditary under exact OLD relational induction. -/
theorem HasValidCompleteMaskDomains.induce
    {E : RelStructure (L.wholeMaskPatternLanguage P) V}
    (h : HasValidCompleteMaskDomains E) (S : Set V) :
    HasValidCompleteMaskDomains (E.induce S) := by
  intro p q t ht
  have hAmbient : E.rel (.inr (.inr (p,q))) (Subtype.val ∘ t) := ht
  obtain ⟨hInj,hDomain⟩ := h p q (Subtype.val ∘ t) hAmbient
  constructor
  · intro i j hij
    apply hInj
    exact congrArg Subtype.val hij
  · change E.rel (.inr (.inl (p,q)))
      (Subtype.val ∘ (fun i : Fin p.rootSize =>
        t (Fin.castAdd q.size i)))
    exact hDomain

/-- Exact equivalence between the SOURCE complete-tuple closed-set
predicate and the 2019 relative U-substructure predicate. It does
not require ambient U-closedness, only well-formed old incidences
and positive primitive input arities. -/
theorem isClosedByWholeMaskTuples_iff_Usubstructure
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (hValid : HasValidCompleteMaskDomains E)
    (hPos : L.PositiveFuncArity)
    (Q : Set V) :
    IsClosedByWholeMaskTuples E Q ↔
      IsUSubstructure (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion E) Q := by
  classical
  constructor
  · intro hClosed rule hrule t ht hRoot k
    obtain ⟨root, rfl⟩ := hrule
    have hPrefix : ∀ i : Fin root.input.rootSize,
        t (Fin.castAdd root.mask.size i) ∈ Q := by
      intro i
      have hIdx : i.castLE root.closureRule.rootLE =
          Fin.castAdd root.mask.size i := by
        apply Fin.ext
        rfl
      rw [← hIdx]
      exact hRoot i
    have hOutput : ∀ j : Fin root.mask.size,
        t (Fin.natAdd root.input.rootSize j) ∈ Q :=
      hClosed root.input root.mask t ht.1 hPrefix
    exact Fin.addCases hPrefix hOutput k
  · intro hU p q t ht hPrefix j
    have hInputPos : 0 < p.rootSize := by
      by_contra hn
      have hZero : p.rootSize = 0 := Nat.eq_zero_of_not_pos hn
      have z : Fin p.rootSize := p.argMap ⟨0, hPos p.symbol⟩
      have z0 : Fin 0 := by simpa only [hZero] using z
      exact Fin.elim0 z0
    have hMaskPos : 0 < q.size :=
      Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    let prefix : Fin p.rootSize → V :=
      fun i => t (Fin.castAdd q.size i)
    obtain ⟨hInj,hDomain⟩ := hValid p q t ht
    let root : Language.WholeMaskRootPattern L P :=
      Language.WholeMaskRootPattern.ofActiveDomain
        E p q hInputPos hMaskPos prefix hDomain
    have hTag : (wholeMaskTagExpansion E).rel (.inr root) t := by
      change E.rel (.inr (.inr (p,q))) t ∧
        ∃ g : Embedding root.root E,
          ∀ i : Fin p.rootSize,
            t (Fin.castAdd q.size i) = g i
      refine ⟨ht,
        Language.WholeMaskRootPattern.ofActiveDomain_embedding
          E p q hInputPos hMaskPos prefix hInj hDomain, ?_⟩
      intro i
      rfl
    have hRoot : ∀ i : Fin root.closureRule.rootSize,
        t (i.castLE root.closureRule.rootLE) ∈ Q := by
      change ∀ i : Fin p.rootSize,
        t (Fin.castAdd q.size i) ∈ Q
      exact hPrefix
    exact hU root.closureRule ⟨root, rfl⟩
      t hTag hRoot (Fin.natAdd p.rootSize j)

end StructuralRamsey.RelStructure
