import PartiteConstruction.Functional.PublishedSparseningLoose
import PartiteConstruction.Functional.WeakBareEHNPullback
import PartiteConstruction.Functional.WeakBareClosedOriginalPartialCompletion

/-!
# Track D: final internal B-copy completion retains strict BARE local rank

English proof FIRST:
docs/track-d-english-ranked-ramsey-final-bcover-20261115.md

Start from ONE actual genuine EHN Stage T with both a full-language
Ramsey arrow and exact weak bare rank n. The independently verified
class-preserving loose B-tree completion yields a final genuine C
with Ramsey arrow, internal B-copy coverage, and an EHN map C -> T.

By the verified bare-rank pullback, C retains its own STRICT
full-functional B-tree local targets on every exact weak n-test,
even though C itself is only a LOOSE functional B-tree.
Closed tests then admit the original 2019 partial-function
strict tree completion at the exact original vertex bound.

This is conditional on finding the ranked Ramsey input Stage T.
No control-budget existence, native unrestricted n-pass, or
false total-fibre projection is asserted.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V P : Type v}

/-- Once a genuine EHN Stage over D has BOTH a full-function Ramsey
arrow and BARE strict full-functional weak locality rank n,
the final genuine B-copy extension can be carried out WITHOUT losing
either property. The SAME resulting C has class membership,
the full Ramsey arrow, genuine original-2019 source-defined partial
projection to D, INTERNAL irreducible B-copy coverage, a loose
B-tree decomposition, and strict B-tree completions of every
literal closed test S of size <= n.

Functions may have any arity including zero and multivalued outputs.
An original-2019 partial projection does not reflect undefinedness. -/
theorem sparseningRamsey_bareRank_withBCover_of_stage
    (K : StructureClass (L := L)) (hK : FreeAmalgamationClass K)
    (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (T : FunctionalPartite.EHN.Stage K D)
    (hArrowT : Arrow A B T.system.toStructure κ)
    (n : ℕ)
    (hBareT : SetAmbientRelativeWeakTreeWitness.AtMostBare
      B T.system.toStructure n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Arrow A B C κ ∧
      (∃ p : W → P,
        IsOriginalPartialHomomorphismEmbedding C D p) ∧
      SetAmbientRelativeWeakTreeWitness.AtMostBare B C n ∧
      IrreduciblesExtendTo B C ∧
      LooseTreeAmalgam B W C ∧
      (∀ S : Finset W, S.card ≤ n →
        ∀ hClosed : C.IsClosed (↑S : Set W),
          HasOriginalPartialTreeCompletion
            B (C.induce (↑S : Set W) hClosed)) := by
  classical
  letI : Finite T.Carrier := T.finiteCarrier
  obtain ⟨W, hW, C, hKC, hArrowC, hp, hLoose, hCover, _hLooseLocal⟩ :=
    sparseningRamsey_functional_looseFullTrees_inClass
      K hK A B T.system.toStructure hKA hKB κ hArrowT
  obtain ⟨q, hq⟩ := hp
  have hBareC :
      SetAmbientRelativeWeakTreeWitness.AtMostBare B C n :=
    SetAmbientRelativeWeakTreeWitness.AtMostBare.pullback_ehn
      hq n hBareT
  have hpToD : C.IsEHNHomomorphismEmbedding
      D (T.system.part ∘ q) :=
    T.isPartite.comp hq
  have hOriginal : IsOriginalPartialHomomorphismEmbedding
      C D (T.system.part ∘ q) :=
    hpToD.toOriginalPartial
  refine ⟨W, hW, C, hKC, hArrowC,
    ⟨T.system.part ∘ q, hOriginal⟩,
    hBareC, hCover, hLoose, ?_⟩
  intro S hCard hClosed
  exact
    SetAmbientRelativeWeakTreeWitness.AtMostBare.closedTest_originalPartialCompletion
      n hBareC S hCard hClosed

end StructuralRamsey.Structure
