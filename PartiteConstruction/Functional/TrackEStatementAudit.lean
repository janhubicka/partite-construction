import PartiteConstruction.Functional.NativeIteratedFinalBCover
import PartiteConstruction.Functional.PublishedTotalBinaryObstruction
import PartiteConstruction.Functional.ClosedTestGraphTreeObstruction
import PartiteConstruction.Functional.ProjectedLooseCompletion
import PartiteConstruction.Functional.FibreExactness

/-!
# Appendix A, independent Track E: exact conclusion contracts

This file compares propositions on the SAME actual witness C, function map p,
and exact test S. It introduces no conditional tree oracle and changes no
proved construction. In particular the printed total-fibre global map is NOT
a consequence of a native EHN / original-2019 partial projection.

The graph-to-full-functional counterexample is reused without weakening its
closed source or changing the tested vertex carrier.
-/

namespace StructuralRamsey.Structure.TrackEStatementAudit

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W P : Type v}

/-- A full survey fibre-surjective homomorphism-embedding implies the genuine
2019 source-defined homomorphism-embedding on the IDENTICAL map. -/
theorem totalHE_implies_originalPartialHE
    {A : Structure L U} {B : Structure L V} {p : U → V}
    (hp : A.IsHomomorphismEmbedding B p) :
    IsOriginalPartialHomomorphismEmbedding A B p := by
  refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
  intro F x _
  exact hp.1.2 F x

/-- The exact missing condition for the converse is reflection of the target
function's defined input domain. No fibre is changed or replaced. -/
theorem originalPartialHE_implies_totalHE_of_domainReflection
    {A : Structure L U} {B : Structure L V} {p : U → V}
    (hp : IsOriginalPartialHomomorphismEmbedding A B p)
    (hreflect : ∀ F (x : Fin (L.funcArity F) → U),
      (B.func F (p ∘ x)).Nonempty → (A.func F x).Nonempty) :
    A.IsHomomorphismEmbedding B p := by
  exact ⟨hp.toEHN.isHomomorphism_of_domainReflection hreflect, hp.2⟩

/-- On a fixed p, the two homomorphism-embedding notions coincide EXACTLY
when the weak map also reflects nonemptiness of all function fibres. -/
theorem totalHE_iff_originalPartialHE_and_domainReflection
    {A : Structure L U} {B : Structure L V} {p : U → V} :
    A.IsHomomorphismEmbedding B p ↔
      IsOriginalPartialHomomorphismEmbedding A B p ∧
      (∀ F (x : Fin (L.funcArity F) → U),
        (B.func F (p ∘ x)).Nonempty → (A.func F x).Nonempty) := by
  constructor
  · intro hp
    refine ⟨totalHE_implies_originalPartialHE hp, ?_⟩
    intro F x ⟨y, hy⟩
    have hImage : y ∈ imageSet p (A.func F x) := by
      rw [hp.1.2 F x]
      exact hy
    obtain ⟨z, hz, _⟩ := hImage
    exact ⟨z, hz⟩
  · rintro ⟨hp, hreflect⟩
    exact originalPartialHE_implies_totalHE_of_domainReflection hp hreflect

/-- Internal ACTUAL B-copies and a fixed EHN projection imply external
projected B-coverage, provided B itself is irreducible. This is ONE-WAY:
the external copy lies in D, not in C. -/
theorem internalCover_implies_projectedCover_of_baseIrreducible
    {Base : Structure L V} {C : Structure L W}
    {D : Structure L P} {p : W → P}
    (hBase : Base.Irreducible)
    (hInternal : IrreduciblesExtendTo Base C)
    (hp : C.IsEHNHomomorphismEmbedding D p) :
    ProjectsIrreduciblesInto Base C D p := by
  intro Y E hE e
  have hS : C.IsClosed (Set.range e) := e.range_isClosed
  have hIrr : (C.induce (Set.range e) hS).Irreducible :=
    hE.range_homomorphism e.isHomomorphism
  obtain ⟨j, hj⟩ := hInternal (Set.range e) hS hIrr
  obtain ⟨beta, hbeta⟩ := hp.2 Base hBase j
  refine ⟨beta, ?_⟩
  intro x
  obtain ⟨b, hb⟩ := hj ⟨e x, ⟨x, rfl⟩⟩
  exact ⟨b, (congrArg p hb).trans (hbeta b).symm⟩

/-- Non-vacuous same-witness positive sanity test: the one-copy case has
both internal and external coverage, with the identity projection. -/
theorem oneCopy_internal_and_external (Base : Structure L V) :
    IrreduciblesExtendTo Base Base ∧
    ProjectsIrreduciblesInto Base Base Base id := by
  have hTree : LooseTreeAmalgam Base V Base :=
    LooseTreeAmalgam.copy (Embedding.id Base) (by
      intro x
      exact ⟨x, rfl⟩)
  exact ⟨hTree.irreduciblesExtendTo,
    ProjectsIrreduciblesInto.base (Embedding.id Base)⟩

/-- External coverage in D is not internal B-copy extension in C.
The witness uses actual finite left-projection algebras: C has 1 vertex,
B=D has 2 vertices. EVERY projected vertex is in B=D, yet B cannot
fully embed inside C. -/
theorem projectedCover_doesNot_imply_internalCover :
    ProjectsIrreduciblesInto
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B
      (fun _ => (0 : Fin 2)) ∧
    ¬ IrreduciblesExtendTo
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.A := by
  constructor
  · intro Y E _ e
    refine ⟨Embedding.id PublishedTotalBinaryObstruction.B, ?_⟩
    intro x
    exact ⟨(0 : Fin 2), rfl⟩
  · intro hInternal
    have hS : PublishedTotalBinaryObstruction.A.IsClosed Set.univ := by
      intro F x hx y hy
      trivial
    have hIrr :
        (PublishedTotalBinaryObstruction.A.induce Set.univ hS).Irreducible := by
      apply PublishedTotalBinaryObstruction.total_irreducible
      intro x y
      exact ⟨x, rfl⟩
    obtain ⟨j, _⟩ := hInternal Set.univ hS hIrr
    have heq : (0 : Fin 2) = 1 :=
      j.injective (Subsingleton.elim (j 0) (j 1))
    exact (by decide : (0 : Fin 2) ≠ 1) heq

/-- The proven graph-tree local endpoint cannot upgrade to a strict full
functional target even for a CLOSED whole source. The test and graph are the
ones of the original finite unary path counterexample. -/
theorem closedWhole_graphTree_not_fullFunctionTree :
    (Structure.ofGraph
      FunctionalClosedTestGraphObstruction.pathGraph).IsClosed Set.univ ∧
    RelStructure.HasTreeCompletion
      FunctionalTreeTransferObstruction.base.graph
      (Structure.ofGraph FunctionalClosedTestGraphObstruction.pathGraph).graph ∧
    ¬ HasTreeCompletion FunctionalTreeTransferObstruction.base
      (Structure.ofGraph FunctionalClosedTestGraphObstruction.pathGraph) :=
  FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion

/-- The paper's literal triple of total-fibre projection, strict function
locality, and internal B-copies is refuted at EVERY n, although the input
Ramsey arrow holds. The counterexample has positive-arity functions and
irreducible A/B. -/
theorem literal_publishedTriple_false_atEveryRank :
    PublishedTotalBinaryObstruction.language.PositiveFuncArity ∧
    PublishedTotalBinaryObstruction.A.Irreducible ∧
    PublishedTotalBinaryObstruction.B.Irreducible ∧
    Arrow PublishedTotalBinaryObstruction.A
      PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.D (Fin 2) ∧
    (∀ n, ¬ PublishedSparseningConclusion
      PublishedTotalBinaryObstruction.A PublishedTotalBinaryObstruction.B
      PublishedTotalBinaryObstruction.D (Fin 2) n) :=
  PublishedTotalBinaryObstruction.published_functional_counterexample

/-- A separate H-valued FULL completion condition on every exact weak
finite test. An H-target is not a claim that the original C itself lies in H.
Every input S is used literally; there is no generated hull. -/
def HasExactWeakHCompletions
    (H : StructureClass (L := L)) (C : Structure L W) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∃ (Y : Type v) (_ : Finite Y) (T : Structure L Y),
      H T ∧
      ∃ f : (↑S : Set W) → Y,
        (C.weakInduce (↑S : Set W)).IsHomomorphismEmbedding T f

/-- A sufficient same-S bridge is WEAK hereditary membership; mere
closed-hereditary membership of H is not silently substituted. -/
theorem exactWeakHCompletions_of_weakHereditary
    (H : StructureClass (L := L)) (C : Structure L W) (n : ℕ)
    (hWeakHer : ∀ {Y : Type v} (T : Structure L Y) (S : Set Y),
      H T → H (T.weakInduce S))
    (hMem : H C) :
    HasExactWeakHCompletions H C n := by
  classical
  intro S _
  let Sset : Set W := (↑S : Set W)
  refine ⟨Sset, inferInstance, C.weakInduce Sset,
    hWeakHer C Sset hMem, ?_⟩
  exact ⟨id, (Embedding.id _).isHomomorphismEmbedding⟩

end StructuralRamsey.Structure.TrackEStatementAudit
