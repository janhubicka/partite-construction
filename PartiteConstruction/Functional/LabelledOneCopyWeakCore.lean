import PartiteConstruction.Functional.NativeStrictWeakHistoryBases
import PartiteConstruction.Functional.LabelledStrictFunctionalTreeGlue

/-!
# Marked and labelled one-copy completion of the native functional HJ core

The marked-A labelled strict target-gluing theorem requires each side to
carry a genuine EHN projection into the control D and a FULL marked
A-copy whose ENTIRE label equals the selected alpha:A↪D.

The pure Hales-Jewett CORE side has this stronger property immediately
whenever the selected alpha extends through one actual Base placement:
  A --eAB--> Base --beta--> D, with beta∘eAB = alpha.

For any EHN core projection p:C→A and ANY exact WEAK vertex test S,
take the one-copy strict Base target, choose f=eAB∘p on S, and label
its vertices by beta. This is an ambient-relative weak HE, preserves
all actual ambient A-copy intersections and EVERY projected-history
predicate, and gives a full marked A-copy in an irreducible constituent
with label alpha on *all* A vertices, including ones not in S.

All operations are genuine and potentially set-valued. The target's
label projection is a FULL embedding beta, so each output fibre is
transversal. No closure hull and no reflection of undefined inputs.

This settles the stronger marked/labelled PURE CORE witness. It does
not yet supply matching marked/labelled completions for arbitrary
OLD-PICTURE weak sides of maximal mixed HJ attachments. In particular
it does not bypass the known odd-cycle counterexample to a uniform
hard-root extension assertion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UC UA VB P : Type v}

/-- For a genuine EHN source core C→A and an actual labelled
placement A↪Base↪D, every exact weak core test has a one-copy
strict FULL-FUNCTIONAL Base-tree witness with a control labelling,
a marked full A-copy, all actual ambient A-copy intersections,
all projected histories, and transversal output fibres.

This is exactly the strong pure-core input of the marked-A mixed
gluing criterion, with NO singleton-valuedness hypothesis. -/
theorem IsEHNHomomorphismEmbedding.labelledOneCopyWeakHistory
    {C : Structure L UC} {A : Structure L UA}
    {Base : Structure L VB} {D : Structure L P}
    {p : UC → UA}
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (eAB : Embedding A Base)
    (beta : Embedding Base D)
    (alpha : Embedding A D)
    (hMark : ∀ a, beta (eAB a) = alpha a)
    (S : Set UC) (history : List (Set P)) :
    ∃ f : S → VB,
      TreeAmalgam Base VB Base ∧
      IsAmbientRelativeWeakHE C S Base f ∧
      SetAmbientACopyIntersections A C Base S f ∧
      (∀ x : S, beta (f x) = alpha (p x.1)) ∧
      SetRespectsProjectedHistory (alpha ∘ p) S f history ∧
      eAB.ContainedInIrreducible ∧
      (∀ F (x : Fin (L.funcArity F) → VB),
        Set.InjOn beta (Base.func F x)) := by
  let f : S → VB := fun x => eAB (p x.1)
  have hTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun x => ⟨x, rfl⟩)
  have hWeak : IsAmbientRelativeWeakHE C S Base f :=
    hp.ambientRelativeWeak_to_embedding eAB S
  have hCopies : SetAmbientACopyIntersections A C Base S f := by
    intro e
    obtain ⟨g, hg⟩ := hp.2 A hA e
    let eT : Embedding A Base := eAB.comp g
    have hContained : eT.ContainedInIrreducible := by
      refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
      intro a
      exact ⟨eT a, rfl⟩
    refine ⟨eT, hContained, ?_⟩
    intro a ha
    change eAB (g a) = eAB (p (e a))
    exact congrArg eAB (hg a)
  have hLabels : ∀ x : S, beta (f x) = alpha (p x.1) :=
    fun x => hMark (p x.1)
  have hHist : SetRespectsProjectedHistory
      (alpha ∘ p) S f history := by
    intro K _hK x y hxy
    have heq : alpha (p x.1) = alpha (p y.1) := by
      calc
        alpha (p x.1) = beta (f x) := (hLabels x).symm
        _ = beta (f y) := congrArg beta hxy
        _ = alpha (p y.1) := hLabels y
    change alpha (p x.1) ∈ K ↔ alpha (p y.1) ∈ K
    rw [heq]
  have hMarkContained : eAB.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro a
    exact ⟨eAB a, rfl⟩
  have hTransversal :
      ∀ F (x : Fin (L.funcArity F) → VB),
        Set.InjOn beta (Base.func F x) := by
    intro F x y _hy z _hz hEq
    exact beta.injective hEq
  exact ⟨f, hTree, hWeak, hCopies, hLabels,
    hHist, hMarkContained, hTransversal⟩

end StructuralRamsey.Structure
