import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.NativePowerTransversalTree
import PartiteConstruction.Functional.InitialTreeCompletion
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# True BASE cases of the strict native functional weak-history invariant

The published functional sparsening proof runs genuinely functional
Hales-Jewett Pictures after its independently verified recursive
Ramsey theorem. The induction must control arbitrary EXACT weak
vertex tests, retaining both (i) full embeddings of intersections
with ACTUAL ambient A-copies and (ii) arbitrary projected histories.

This file proves these exact strict FULL-FUNCTION-TREE targets for:
  1. ANY genuine strict functional B-tree, via inclusion of the weak test;
  2. ANY EHN source C with projection to an irreducible A embedded in an
     irreducible Base B, via the one-copy Base-tree target;
  3. the ACTUAL initial EHN Picture assembled from full B-placements;
  4. the ACTUAL functional Hales-Jewett power core, with all
     set-valued function output fibres TRANSVERSAL in their parts.

No singleton hypothesis, unbounded root extension oracle, closure of
the tested S, graph-tree replacement, or renewed Ramsey recursion is
used. These are the pure/initial cases; the maximal-rank genuinely
mixed selected-support attachment remains the target-side obstacle.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U VB W P : Type v}

namespace SetAmbientRelativeWeakTreeWitness

/-- An actual strict functional B-tree satisfies the full
source-relative weak-test completion invariant at every exact
vertex set and every list of projected history predicates.

The tested subset is NOT required to be function-closed: the weak
inclusion preserves positive function incidences and complete
fibres precisely where no ambient output was discarded. -/
theorem of_strict_tree
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W}
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (hTree : TreeAmalgam Base W C)
    (p : W → P) (S : Set W) (history : List (Set P)) :
    SetAmbientRelativeWeakTreeWitness A Base C p S history := by
  let inc : S → W := Subtype.val
  have hRel : IsAmbientRelativeWeakHE C S C inc :=
    (Embedding.id C).ambientRelativeWeakRestriction S
  refine ⟨W, C, hTree, inc, hRel, ?_, ?_⟩
  · intro e
    obtain ⟨baseCopy, hContains⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy
        hA e
    refine ⟨e, ?_, ?_⟩
    · exact ⟨VB, Base, hBase, baseCopy, hContains⟩
    · intro a ha
      rfl
  · intro H _hH x y hxy
    have heq : x = y := Subtype.val_injective hxy
    subst y
    exact Iff.rfl

/-- Every weak test in an EHN source C projecting to an
irreducible functional A with a full embedding A→Base has a
STRICT one-copy Base-tree completion controlling ALL genuine
ambient A-copy intersections and arbitrary projected histories.

The map is eAB ∘ p; full embeddings of A-copies come from the
EHN irreducible clause, and kernel compatibility of histories
uses only eAB.injective (NOT global injectivity of p).
All set-valued fibres may be multivalued, but in the actual
partite application they are transversal in their parts. -/
theorem of_ehn_oneCopy
    (A : Structure L U) (Base : Structure L VB)
    (C : Structure L W) {p : W → U}
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    (S : Set W) (history : List (Set U)) :
    SetAmbientRelativeWeakTreeWitness A Base C p S history := by
  let f : S → VB := fun x => eAB (p x.1)
  have hWeak : IsAmbientRelativeWeakHE C S Base f :=
    hp.ambientRelativeWeak_to_embedding eAB S
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  refine ⟨VB, Base, hTree, f, hWeak, ?_, ?_⟩
  · intro e
    obtain ⟨g, hg⟩ := hp.2 A hA e
    let eT : Embedding A Base := eAB.comp g
    have hContained : eT.ContainedInIrreducible := by
      refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
      intro a
      exact ⟨eT a, rfl⟩
    refine ⟨eT, hContained, ?_⟩
    intro a ha
    exact congrArg eAB (hg a)
  · intro H _hH x y hxy
    have hProj : p x.1 = p y.1 := by
      apply eAB.injective
      exact hxy
    rw [hProj]

end SetAmbientRelativeWeakTreeWitness

end StructuralRamsey.Structure


namespace StructuralRamsey.FunctionalPartite.EHN

open Structure

universe u v
variable {L : Language.{u}}
variable {P U V : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The ACTUAL native initial EHN Picture already satisfies strict
full-functional B-tree completion of EVERY exact weak test, with
actual full ambient A-copy intersections and arbitrary projected
history predicates. It also retains all B placements into D.

Only A and B irreducible are required: there is no hereditary
irreducibility hypothesis on all closed partial A-pieces. -/
theorem initial_weakHistory_strictTree
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (hA : A.Irreducible)
    (Base : Structure L V) [Finite V] [Finite P]
    (hBaseMem : K Base) (hBaseIrred : Base.Irreducible)
    (hpos : L.PositiveFuncArity)
    (beta0 : Structure.Embedding Base D) :
    ∃ T : Stage K D,
      (∀ (S : Set T.Carrier) (history : List (Set P)),
        SetAmbientRelativeWeakTreeWitness A Base
          T.system.toStructure T.system.part S history) ∧
      (∀ beta : Structure.Embedding Base D,
        ∃ e : Structure.Embedding Base T.system.toStructure,
          ∀ x, T.system.part (e x) = beta x) := by
  obtain ⟨T, hTree, hCopies⟩ :=
    initial_tree hK Base hBaseMem hBaseIrred hpos beta0
  refine ⟨T, ?_, hCopies⟩
  intro S history
  exact SetAmbientRelativeWeakTreeWitness.of_strict_tree
    hA hBaseIrred hTree T.system.part S history

end StructuralRamsey.FunctionalPartite.EHN


namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V VB : Type v}

/-- A genuine functional Hales-Jewett coordinate power enjoys BOTH
the required transversality of every set-valued output fibre and
strict one-copy Base-tree witnesses for every exact weak test
with actual A-copy histories and arbitrary projected diaries.

This is a pure core result: it does not assume the false arbitrary
maximal-mixed-root extension schema. -/
theorem power_strictWeakHistory_transversal
    (A : Structure L P) (B : System L P V)
    (hB : B.WeaklyPartiteOver A)
    (N : ℕ) (hN : 0 < N)
    (Base : Structure L VB)
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (eAB : Structure.Embedding A Base) :
    (∀ F (x : Fin (L.funcArity F) → Vertex B N),
      Set.InjOn (power B N).part ((power B N).func F x)) ∧
    ∀ (S : Set (Vertex B N)) (history : List (Set P)),
      SetAmbientRelativeWeakTreeWitness A Base
        (power B N).toStructure (power B N).part S history := by
  constructor
  · intro F x
    exact (power B N).func_part_injOn F x
  · intro S history
    have hPower : (power B N).WeaklyPartiteOver A :=
      power_weaklyPartiteOver hB hN
    exact SetAmbientRelativeWeakTreeWitness.of_ehn_oneCopy
      A Base (power B N).toStructure
      hPower hA hBase eAB S history

end StructuralRamsey.FunctionalPartite.Induced
