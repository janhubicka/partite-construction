import PartiteConstruction.Functional.WholeMaskTargetOutputHull2019
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Coherent complete values across output-mask enumerations

An arbitrary U-closed tagged target may have two OLD complete output
tuples for the same equality-pattern symbol and the same whole input
root, using distinct output-part lists. U-closedness alone compares
only tuples bearing exactly the same fresh closure symbol.

Full-root normality, valid OLD domains, and positive primitive input
arity place both complete output tuples inside ONE U-hull generated
by their common input root. The active domain relation makes that
root an ordinary irreducible seed. The protected final B-copy
coverage therefore fully embeds its hull into canonical B, where
the two OLD tuples give the SAME genuine partial-function value.
Injectivity of the embedding reflects equality of complete source
output SETS, not of arbitrary enumerations.

The U-hull is only a target witness used in this comparison. It never
replaces an exact weak test or alters its induction rank.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- In a normal final U-closed target with canonical B-copy coverage,
any two complete output lists for the SAME equality-pattern symbol and
the SAME distinct-input root have equal underlying output VERTEX sets.
The lists may use different output-part orderings and lengths. -/
theorem WholeMaskTagNormal.completeValue_unique_sameRoot_of_covered
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
    (p : Language.FunctionInputPattern L)
    (q₁ q₂ : Language.CompleteOutputParts P)
    (t₁ : Fin (p.rootSize + q₁.size) → V)
    (t₂ : Fin (p.rootSize + q₂.size) → V)
    (ht₁ : (wholeMaskTagReduct C).rel
      (.inr (.inr (p,q₁))) t₁)
    (ht₂ : (wholeMaskTagReduct C).rel
      (.inr (.inr (p,q₂))) t₂)
    (hRoot : ∀ i : Fin p.rootSize,
      t₁ (Fin.castAdd q₁.size i) =
      t₂ (Fin.castAdd q₂.size i)) :
    Set.range (fun j : Fin q₁.size =>
      t₁ (Fin.natAdd p.rootSize j)) =
    Set.range (fun j : Fin q₂.size =>
      t₂ (Fin.natAdd p.rootSize j)) := by
  classical
  let root : Fin p.rootSize → V :=
    fun i => t₁ (Fin.castAdd q₁.size i)
  let S : Set V := Set.range root
  let H : Set V :=
    UClosureHull (L.wholeMaskClosureRules P) C S
  have hDom : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q₁))) root :=
    (hValid p q₁ t₁ ht₁).2
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q₁)))) root hDom
  obtain ⟨g⟩ := hCover (C.induce H)
    (hC.induce_UClosureHull S)
    (hC.irreducibleSeed_hull_isUIrreducible S hIrred)
    (inclusion C H)
  have hPref₁ : ∀ i : Fin p.rootSize,
      t₁ (Fin.castAdd q₁.size i) ∈ H := by
    intro i
    exact subset_UClosureHull
      (L.wholeMaskClosureRules P) C S ⟨i, rfl⟩
  have hPref₂ : ∀ i : Fin p.rootSize,
      t₂ (Fin.castAdd q₂.size i) ∈ H := by
    intro i
    rw [← hRoot i]
    exact hPref₁ i
  have hOut₁ : ∀ j : Fin q₁.size,
      t₁ (Fin.natAdd p.rootSize j) ∈ H := by
    intro j
    exact hNormal.completeOutput_mem_inputHull
      C hValid hPos p q₁ t₁ ht₁ j
  have hOut₂ : ∀ j : Fin q₂.size,
      t₂ (Fin.natAdd p.rootSize j) ∈ H := by
    intro j
    have hRange : Set.range (fun i : Fin p.rootSize =>
        t₂ (Fin.castAdd q₂.size i)) = S := by
      change Set.range (fun i : Fin p.rootSize =>
        t₂ (Fin.castAdd q₂.size i)) = Set.range root
      congr 1
      funext i
      exact (hRoot i).symm
    have h := hNormal.completeOutput_mem_inputHull
      C hValid hPos p q₂ t₂ ht₂ j
    simpa only [hRange] using h
  have hAll₁ : ∀ k : Fin (p.rootSize + q₁.size), t₁ k ∈ H :=
    fun k => Fin.addCases hPref₁ hOut₁ k
  have hAll₂ : ∀ k : Fin (p.rootSize + q₂.size), t₂ k ∈ H :=
    fun k => Fin.addCases hPref₂ hOut₂ k
  let t₁H : Fin (p.rootSize + q₁.size) → H :=
    fun k => ⟨t₁ k, hAll₁ k⟩
  let t₂H : Fin (p.rootSize + q₂.size) → H :=
    fun k => ⟨t₂ k, hAll₂ k⟩
  have hB₁ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p,q₁))) (g ∘ t₁H) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q₁)))) t₁H).mpr ht₁
  have hB₂ : (Base.wholeMaskPatternGraph part).rel
      (.inr (.inr (p,q₂))) (g ∘ t₂H) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q₂)))) t₂H).mpr ht₂
  let inp₁ : Fin (L.funcArity p.symbol) → W :=
    (fun i : Fin p.rootSize =>
      g (t₁H (Fin.castAdd q₁.size i))) ∘ p.argMap
  let inp₂ : Fin (L.funcArity p.symbol) → W :=
    (fun i : Fin p.rootSize =>
      g (t₂H (Fin.castAdd q₂.size i))) ∘ p.argMap
  let out₁ : Fin q₁.size → W :=
    fun j => g (t₁H (Fin.natAdd p.rootSize j))
  let out₂ : Fin q₂.size → W :=
    fun j => g (t₂H (Fin.natAdd p.rootSize j))
  have hVal₁ : Base.func p.symbol inp₁ = some (Set.range out₁) :=
    hB₁.2.1
  have hVal₂ : Base.func p.symbol inp₂ = some (Set.range out₂) :=
    hB₂.2.1
  have hInp : inp₁ = inp₂ := by
    funext i
    change g (t₁H (Fin.castAdd q₁.size (p.argMap i))) =
      g (t₂H (Fin.castAdd q₂.size (p.argMap i)))
    apply congrArg g
    apply Subtype.ext
    exact hRoot (p.argMap i)
  have hOutputEq : Set.range out₁ = Set.range out₂ :=
    Option.some.inj
      (hVal₁.symm.trans
        ((congrArg (Base.func p.symbol) hInp).trans hVal₂))
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    have hIn : out₁ j ∈ Set.range out₂ := by
      rw [← hOutputEq]
      exact ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hIn
    have hEq : t₁H (Fin.natAdd p.rootSize j) =
        t₂H (Fin.natAdd p.rootSize k) :=
      g.injective hk.symm
    exact ⟨k, (congrArg Subtype.val hEq).symm⟩
  · rintro ⟨k, rfl⟩
    have hIn : out₂ k ∈ Set.range out₁ := by
      rw [hOutputEq]
      exact ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := hIn
    have hEq : t₂H (Fin.natAdd p.rootSize k) =
        t₁H (Fin.natAdd p.rootSize j) :=
      g.injective hj.symm
    exact ⟨j, (congrArg Subtype.val hEq).symm⟩

end StructuralRamsey.RelStructure
