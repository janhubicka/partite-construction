import PartiteConstruction.Functional.WholeMaskCoveredOutputSameRoot2019
import PartiteConstruction.Functional.PatternDecodedOutputHull2019
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Complete values do not depend on equality-pattern presentations

An arbitrary canonical-tag-normal, U-closed final target may describe
one primitive input tuple by distinct input equality-patterns: different
surjections, distinct-root enumerations, and full OLD input patterns.
Their closure symbols are distinct, so ordinary U-closedness alone
does not equate their complete outputs.

For positive-arity F the root of EACH presentation has exactly the
same range as the original input tuple. The active domain relation of
one presentation makes this exact input vertex set an ordinary
irreducible seed. By final protected closed U-irreducible B-copy
coverage, its U-hull embeds FULLY into one canonical genuine partial
function structure B.

Tag normality and old root validity put all outputs of BOTH patterns
into that ONE input hull. The resulting two OLD output graph tuples
have the same primitive F-input after embedding into B. Since B has a
single Option(Set) value on that input, the two COMPLETE output sets
coincide. Injectivity of the full B embedding reflects equality of
original output vertex sets.

This uses a closure hull ONLY as a target-side comparison witness.
It neither enlarges the exact weak test S nor its projected f[S], and
makes no claim about the still-open strict functional B-tree mixed
completion. Nullary F requires its separate root-free case.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- The entire value SET is independent of which surjective distinct
input-root equality pattern and complete output-part enumeration
represent the SAME actual primitive function tuple x. The final
tagged target has protected closed irreducible B-copy coverage.
No singleton-valuedness hypothesis is used: the output is an
arbitrary finite set, with at most one point in each part only when
a separate transversal-partite assumption is imposed. -/
theorem WholeMaskTagNormal.completeValue_unique_crossPattern_of_covered
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hNormal : WholeMaskTagNormal C)
    (hValid : HasValidCompleteMaskDomains (wholeMaskTagReduct C))
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (F : L.FuncSymbol)
    (m₁ m₂ : ℕ)
    (r₁ : Fin (L.funcArity F) → Fin m₁)
    (r₂ : Fin (L.funcArity F) → Fin m₂)
    (hr₁ : Function.Surjective r₁)
    (hr₂ : Function.Surjective r₂)
    (q₁ q₂ : Language.CompleteOutputParts P)
    (t₁ : Fin (m₁ + q₁.size) → V)
    (t₂ : Fin (m₂ + q₂.size) → V)
    (x : Fin (L.funcArity F) → V)
    (hArgs₁ : ∀ i, x i = t₁ (Fin.castAdd q₁.size (r₁ i)))
    (hArgs₂ : ∀ i, x i = t₂ (Fin.castAdd q₂.size (r₂ i)))
    (hOld₁ : (wholeMaskTagReduct C).rel
      (.inr (.inr ((⟨F, m₁, r₁, hr₁⟩ :
        Language.FunctionInputPattern L),q₁))) t₁)
    (hOld₂ : (wholeMaskTagReduct C).rel
      (.inr (.inr ((⟨F, m₂, r₂, hr₂⟩ :
        Language.FunctionInputPattern L),q₂))) t₂) :
    Set.range (fun j : Fin q₁.size =>
      t₁ (Fin.natAdd m₁ j)) =
    Set.range (fun j : Fin q₂.size =>
      t₂ (Fin.natAdd m₂ j)) := by
  classical
  let p₁ : Language.FunctionInputPattern L :=
    ⟨F, m₁, r₁, hr₁⟩
  let p₂ : Language.FunctionInputPattern L :=
    ⟨F, m₂, r₂, hr₂⟩
  let root₁ : Fin m₁ → V :=
    fun i => t₁ (Fin.castAdd q₁.size i)
  let root₂ : Fin m₂ → V :=
    fun i => t₂ (Fin.castAdd q₂.size i)
  have hFactor₁ : ∀ i, x i = root₁ (r₁ i) := hArgs₁
  have hFactor₂ : ∀ i, x i = root₂ (r₂ i) := hArgs₂
  have hRange₁ : Set.range root₁ = Set.range x :=
    equalityPattern_range_eq x r₁ hr₁ root₁ hFactor₁
  have hRange₂ : Set.range root₂ = Set.range x :=
    equalityPattern_range_eq x r₂ hr₂ root₂ hFactor₂
  let S : Set V := Set.range x
  let H : Set V :=
    UClosureHull (L.wholeMaskClosureRules P) C S
  have hDom : (wholeMaskTagReduct C).rel
      (.inr (.inl (p₁,q₁))) root₁ :=
    (hValid p₁ q₁ t₁ hOld₁).2
  have hIrredRoot : (C.induce (Set.range root₁)).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p₁,q₁)))) root₁ hDom
  have hIrred : (C.induce S).Irreducible := by
    change (C.induce (Set.range x)).Irreducible
    rw [← hRange₁]
    exact hIrredRoot
  obtain ⟨g⟩ := hCover (C.induce H)
    (hC.induce_UClosureHull S)
    (hC.irreducibleSeed_hull_isUIrreducible S hIrred)
    (inclusion C H)
  have hxH (i : Fin (L.funcArity F)) : x i ∈ H :=
    subset_UClosureHull (L.wholeMaskClosureRules P) C S
      ⟨i, rfl⟩
  let xH : Fin (L.funcArity F) → H :=
    fun i => ⟨x i, hxH i⟩
  have hPref₁ : ∀ i : Fin m₁,
      t₁ (Fin.castAdd q₁.size i) ∈ H := by
    intro i
    apply subset_UClosureHull (L.wholeMaskClosureRules P) C S
    change t₁ (Fin.castAdd q₁.size i) ∈ Set.range x
    rw [← hRange₁]
    exact ⟨i, rfl⟩
  have hPref₂ : ∀ i : Fin m₂,
      t₂ (Fin.castAdd q₂.size i) ∈ H := by
    intro i
    apply subset_UClosureHull (L.wholeMaskClosureRules P) C S
    change t₂ (Fin.castAdd q₂.size i) ∈ Set.range x
    rw [← hRange₂]
    exact ⟨i, rfl⟩
  have hOut₁ : ∀ j : Fin q₁.size,
      t₁ (Fin.natAdd m₁ j) ∈ H := by
    intro j
    have hy := hNormal.completeOutput_mem_inputHull
      C hValid hPos p₁ q₁ t₁ hOld₁ j
    change t₁ (Fin.natAdd m₁ j) ∈
      UClosureHull (L.wholeMaskClosureRules P) C (Set.range root₁) at hy
    rw [hRange₁] at hy
    exact hy
  have hOut₂ : ∀ j : Fin q₂.size,
      t₂ (Fin.natAdd m₂ j) ∈ H := by
    intro j
    have hy := hNormal.completeOutput_mem_inputHull
      C hValid hPos p₂ q₂ t₂ hOld₂ j
    change t₂ (Fin.natAdd m₂ j) ∈
      UClosureHull (L.wholeMaskClosureRules P) C (Set.range root₂) at hy
    rw [hRange₂] at hy
    exact hy
  have hAll₁ : ∀ k : Fin (m₁ + q₁.size), t₁ k ∈ H :=
    fun k => Fin.addCases hPref₁ hOut₁ k
  have hAll₂ : ∀ k : Fin (m₂ + q₂.size), t₂ k ∈ H :=
    fun k => Fin.addCases hPref₂ hOut₂ k
  let t₁H : Fin (m₁ + q₁.size) → H :=
    fun k => ⟨t₁ k, hAll₁ k⟩
  let t₂H : Fin (m₂ + q₂.size) → H :=
    fun k => ⟨t₂ k, hAll₂ k⟩
  have hB₁ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p₁,q₁))) (g ∘ t₁H) :=
    (g.map_rel_iff (.inl (.inr (.inr (p₁,q₁)))) t₁H).mpr hOld₁
  have hB₂ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p₂,q₂))) (g ∘ t₂H) :=
    (g.map_rel_iff (.inl (.inr (.inr (p₂,q₂)))) t₂H).mpr hOld₂
  let out₁ : Fin q₁.size → W :=
    fun j => g (t₁H (Fin.natAdd m₁ j))
  let out₂ : Fin q₂.size → W :=
    fun j => g (t₂H (Fin.natAdd m₂ j))
  have hInputs₁ :
      ((fun i : Fin m₁ => g (t₁H (Fin.castAdd q₁.size i))) ∘ r₁) =
      g ∘ xH := by
    funext i
    apply congrArg g
    apply Subtype.ext
    exact (hArgs₁ i).symm
  have hInputs₂ :
      ((fun i : Fin m₂ => g (t₂H (Fin.castAdd q₂.size i))) ∘ r₂) =
      g ∘ xH := by
    funext i
    apply congrArg g
    apply Subtype.ext
    exact (hArgs₂ i).symm
  have hValue₁ : Base.func F (g ∘ xH) =
      some (Set.range out₁) := by
    have hVal := hB₁.2.1
    change Base.func F
        ((fun i : Fin m₁ => g (t₁H (Fin.castAdd q₁.size i))) ∘ r₁) =
        some (Set.range out₁) at hVal
    rw [hInputs₁] at hVal
    exact hVal
  have hValue₂ : Base.func F (g ∘ xH) =
      some (Set.range out₂) := by
    have hVal := hB₂.2.1
    change Base.func F
        ((fun i : Fin m₂ => g (t₂H (Fin.castAdd q₂.size i))) ∘ r₂) =
        some (Set.range out₂) at hVal
    rw [hInputs₂] at hVal
    exact hVal
  have hImageEq : Set.range out₁ = Set.range out₂ :=
    Option.some.inj (hValue₁.symm.trans hValue₂)
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    have hIn : out₁ j ∈ Set.range out₂ := by
      rw [← hImageEq]
      exact ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hIn
    have hEq : t₁H (Fin.natAdd m₁ j) =
        t₂H (Fin.natAdd m₂ k) :=
      g.injective hk.symm
    exact ⟨k, (congrArg Subtype.val hEq).symm⟩
  · rintro ⟨k, rfl⟩
    have hIn : out₂ k ∈ Set.range out₁ := by
      rw [hImageEq]
      exact ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := hIn
    have hEq : t₂H (Fin.natAdd m₂ k) =
        t₁H (Fin.natAdd m₁ j) :=
      g.injective hj.symm
    exact ⟨j, (congrArg Subtype.val hEq).symm⟩

end StructuralRamsey.RelStructure
