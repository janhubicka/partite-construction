import PartiteConstruction.Ramsey.ClosureClosedCompletionRank
import PartiteConstruction.Ramsey.CompatibleClassCompletion
import PartiteConstruction.Ramsey.ClosureEmbeddingRange

/-! # Independent completions agree on a closed projected boundary in K

A special case of the mixed Picture step does NOT need a simultaneous
relative-extension oracle. Suppose the source separator maps into a fixed
closed structure Q embedded in both projected side sources, and Q is a
member of K. Since K consists of irreducible structures, any side completion
must restrict to an embedding of Q. These two restrictions automatically
supply a compatible target diagram over the SAME Q.

The source separator need not be irreducible and its map to Q need not be
injective. Q can be obtained as the closure of its projected vertices inside
a fixed A-copy: U-closed hereditariness gives Q in K, hence irreducibility.
Mere containment in an irreducible A would not imply irreducibility of Q.

The last theorem gives a B-copywise completion. It does not yet give a
completion on all protected tests, prove the rank drop for the projected
side sources, or identify the working convention with Definition 2.17.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V : Type v}

/-- The ambient closure of S contained in a closed A-copy embeds back
into that SAME copy, with the original vertex coordinates. -/
theorem closedHull_factor_closed_copy
    (rules : ClosureDescription L)
    {A : RelStructure L U} {D : RelStructure L V}
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D) (S : Set V) (hS : S ⊆ Set.range a) :
    ∃ e : Embedding (D.induce (UClosureHull rules D S)) A,
      ∀ x, a (e x) = x.1 := by
  classical
  let Q : Set V := UClosureHull rules D S
  have hQ : Q ⊆ Set.range a :=
    UClosureHull_minimal rules D (a.range_isUSubstructure hA hD) hS
  let inc : Embedding (D.induce Q) D := inclusion D Q
  have hRange (x : Q) : ∃ y : U, inc x = a y := by
    obtain ⟨y, hy⟩ := hQ x.2
    exact ⟨y, hy.symm⟩
  let e : Embedding (D.induce Q) A := inc.factorThroughRange a hRange
  refine ⟨e, ?_⟩
  intro x
  exact (Classical.choose_spec (hRange x)).symm

/-- Closed hereditariness, NOT hereditary graph-irreducibility of A,
puts the projected closure in K and makes it ordinarily irreducible. -/
theorem closedHull_in_class_of_subset_copy
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {F : RelStructure L Y},
      K F → IsUClosed rules E → Embedding E F → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    {A : RelStructure L U} {D : RelStructure L V}
    (hKA : K A) (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D) (S : Set V) (hS : S ⊆ Set.range a) :
    K (D.induce (UClosureHull rules D S)) ∧
      (D.induce (UClosureHull rules D S)).Irreducible := by
  obtain ⟨e, _⟩ := closedHull_factor_closed_copy rules hA hD a S hS
  have hKQ := hHereditary hKA (hD.induce_UClosureHull S) e
  exact ⟨hKQ, hKIrr _ hKQ⟩

/-- Independently selected side maps automatically embed the SAME
closed irreducible Q. No prior compatibility between their targets
is assumed. Their agreement is through the original Q coordinates. -/
theorem IsClosedUHomomorphismEmbedding.common_boundary_embeddings
    {P X Y XL YR : Type v}
    {rules : ClosureDescription L}
    {Q : RelStructure L P}
    {DL : RelStructure L X} {DR : RelStructure L Y}
    {TL : RelStructure L XL} {TR : RelStructure L YR}
    {fL : X → XL} {fR : Y → YR}
    (hQ : IsUClosed rules Q) (hQIrr : Q.Irreducible)
    (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hL : IsClosedUHomomorphismEmbedding rules DL TL fL)
    (hR : IsClosedUHomomorphismEmbedding rules DR TR fR) :
    ∃ (eL : Embedding Q TL) (eR : Embedding Q TR),
      (∀ q, eL q = fL (rL q)) ∧
      (∀ q, eR q = fR (rR q)) := by
  obtain ⟨eL, heL⟩ := hL.on_test Q hQ (hQIrr.isUIrreducible rules) rL
  obtain ⟨eR, heR⟩ := hR.on_test Q hQ (hQIrr.isUIrreducible rules) rR
  exact ⟨eL, eR, heL, heR⟩

/-- Existence of compatible B-copywise completion diagrams from
independent K-completions of the two projected sources. The common
closed irreducible Q is fixed BEFORE either completion is chosen.
No injectivity of the source-root map q is required. -/
theorem HasCopywiseCompletion.of_independent_projected_completions
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    {VB H E F C P X Y : Type v}
    {Base : RelStructure L VB}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hBaseClosed : IsUClosed rules Base) (hBase : Base.Irreducible)
    [Finite P]
    (Q : RelStructure L P) (hQK : K Q)
    (hQClosed : IsUClosed rules Q) (hQIrred : Q.Irreducible)
    (DL : RelStructure L X) (DR : RelStructure L Y)
    (pL : E → X) (pR : F → Y)
    (hpL : IsClosedUHomomorphismEmbedding rules Left DL pL)
    (hpR : IsClosedUHomomorphismEmbedding rules Right DR pR)
    (q : H → P) (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hRootL : ∀ d, pL (sL d) = rL (q d))
    (hRootR : ∀ d, pR (sR d) = rR (q d))
    (hDL : HasClosedUKCompletion K rules DL)
    (hDR : HasClosedUKCompletion K rules DR) :
    HasCopywiseCompletion K Base Whole := by
  obtain ⟨XL, hXL, TL, hTL, _, fL, hfL⟩ := hDL
  obtain ⟨YR, hYR, TR, hTR, _, fR, hfR⟩ := hDR
  letI : Finite XL := hXL
  letI : Finite YR := hYR
  obtain ⟨eL, eR, heL, heR⟩ :=
    IsClosedUHomomorphismEmbedding.common_boundary_embeddings
      hQClosed hQIrred rL rR hfL hfR
  have hL : CopywiseCompletion Base Left TL (fL ∘ pL) :=
    (hfL.comp hpL).copywise Base hBaseClosed (hBase.isUIrreducible rules)
  have hR : CopywiseCompletion Base Right TR (fR ∘ pR) :=
    (hfR.comp hpR).copywise Base hBaseClosed (hBase.isUIrreducible rules)
  have hCompatL : ∀ d, (fL ∘ pL) (sL d) = eL (q d) := by
    intro d
    change fL (pL (sL d)) = eL (q d)
    rw [hRootL d]
    exact (heL (q d)).symm
  have hCompatR : ∀ d, (fR ∘ pR) (sR d) = eR (q d) := by
    intro d
    change fR (pR (sR d)) = eR (q d)
    rw [hRootR d]
    exact (heR (q d)).symm
  exact HasCopywiseCompletion.of_compatible_class_diagram hK
    hBase hSrc Q TL TR hQK hTL hTR q (fL ∘ pL) (fR ∘ pR)
    hL hR eL eR hCompatL hCompatR

end StructuralRamsey.RelStructure
