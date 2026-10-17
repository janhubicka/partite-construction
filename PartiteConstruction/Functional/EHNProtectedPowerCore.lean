import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue
import PartiteConstruction.Functional.EHNRealizedPlacementBaseExtension

/-!
# The actual functional Hales--Jewett power has a protected A-collar

The audited protected-mark repair needs two directions on a marked
full copy aT:A↪T of the control A:
  f(x) = aT(a)  ↔  part(x) = alpha(a)
on every vertex of the EXACT weak tested subset.

For an active genuine Hales--Jewett alphabet in an old EHN Stage,
projected irreducible Base-coverage provides beta:Base↪D and
eAB:A↪Base with beta∘eAB=alpha.

The already verified labelled one-copy HJ power witness has
beta(f x)=alpha(part_E x). Injectivity of beta and alpha therefore
gives the precise iff, not merely the weaker anchored or no-wrong-hit
half. The same witness has a STRICT full-functional one-copy
Base-tree, every ambient full A-intersection and arbitrary projected
histories; all output fibres in the genuine power stay transversal.

This proves the POWER CORE base case of the proposed protected-collar
induction, not its preservation across arbitrary mixed attachments.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U VB P : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- An active ACTUAL Hales--Jewett power, projected through alpha,
has a one-copy STRICT Base-tree weak witness with a full protected
marked A-copy, for every exact weak tested set and every finite
projected history.

No singleton-valuedness, enlargement of the tested source, or global
reflection of undefined source function inputs is required. -/
theorem Stage.activePower_protectedWeakCore
    (Old : Stage K D)
    (A : Structure L U) (Base : Structure L VB)
    (hCover : Old.ProjectedCover Base)
    (hA : A.Irreducible) (hBase : Base.Irreducible)
    (alpha : Structure.Embedding A D)
    (hLetters : Nonempty (FunctionalPartite.Embedding
      (transversal A)
      (Old.system.weakRestrict D Old.isPartite.1 A alpha)))
    (N : ℕ) (hN : 0 < N) :
    let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
    let E := Induced.power R N
    ∃ (beta : Structure.Embedding Base D)
      (eAB : Structure.Embedding A Base),
      (∀ a, beta (eAB a) = alpha a) ∧
      (∀ F (x : Fin (L.funcArity F) → Induced.Vertex R N),
        Set.InjOn E.part (E.func F x)) ∧
      ∀ (S : Set (Induced.Vertex R N))
        (history : List (Set P)),
        ∃ f : S → VB,
          TreeAmalgam Base VB Base ∧
          IsAmbientRelativeWeakHE E.toStructure S Base f ∧
          SetAmbientACopyIntersections A E.toStructure Base S f ∧
          SetRespectsProjectedHistory
            (alpha ∘ E.part) S f history ∧
          ProtectedAMark alpha (alpha ∘ E.part) S f eAB ∧
          eAB.ContainedInIrreducible := by
  classical
  dsimp only
  let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
  let E := Induced.power R N
  obtain ⟨beta, eAB, hAlpha, hTrans, hWitness⟩ :=
    Old.activePower_labelledWeakCore
      A Base hCover hA hBase alpha hLetters N hN
  refine ⟨beta, eAB, hAlpha, hTrans, ?_⟩
  intro S history
  obtain ⟨f, hTree, hWeak, hCopies, hLabels, hHist, hContained⟩ :=
    hWitness S history
  have hAnchored : ∀ (x : S) (a : U),
      (alpha ∘ E.part) x.1 = alpha a →
      f x = eAB a := by
    intro x a hx
    apply beta.injective
    calc
      beta (f x) = alpha (E.part x.1) := hLabels x
      _ = alpha a := hx
      _ = beta (eAB a) := (hAlpha a).symm
  have hProtected : ProtectedAMark
      alpha (alpha ∘ E.part) S f eAB :=
    ProtectedAMark.of_labelled alpha (alpha ∘ E.part)
      S f eAB beta hLabels hAlpha hAnchored
  exact ⟨f, hTree, hWeak, hCopies, hHist, hProtected, hContained⟩

end StructuralRamsey.FunctionalPartite.EHN
