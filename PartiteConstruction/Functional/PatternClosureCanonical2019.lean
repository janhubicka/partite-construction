import PartiteConstruction.Functional.PatternClosureTags2019

/-!
# Canonical singleton-valued functions satisfy the fresh 2019 closure rules

Every canonical active root of a partial function is recorded by its
FULL old relational input pattern, including its domain relation.
The corresponding fresh tag is a single-valued output graph relation.

For a singleton-valued primitive target, every embedding of that full
root into the canonical tagged graph has a UNIQUE output tuple.
Moreover every tagged output tuple has an actual embedded root.

This is the canonical direction of the 2019 closure-description
bridge. The converse, namely coherence of arbitrary tagged closed
Pictures, requires separate normalization/validity lemmas.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A canonical tagged pattern graph of a genuinely partial
singleton-valued function structure is U-closed under ALL fresh
positive root-pattern rules. No distinct-input or order assumption
is placed on the original primitive function arguments. -/
theorem patternTagExpansion_isUClosed
    (A : Structure L V) (hA : A.SingletonValued) :
    IsUClosed (L.patternClosureRules)
      (patternTagExpansion A.patternGraph) := by
  classical
  intro rule hrule
  obtain ⟨p, rfl⟩ := hrule
  constructor
  · intro t ht
    change
      (A.patternGraph).rel (.inr (.inr p.input)) t ∧
      ∃ e : Embedding p.root A.patternGraph,
        ∀ i : Fin p.input.rootSize, t i.castSucc = e i at ht
    obtain ⟨_, e, he⟩ := ht
    exact ⟨e.patternTag, he⟩
  · intro e
    let old : Embedding p.root A.patternGraph :=
      e.patternTagReduct
    let root : Fin p.input.rootSize → V := fun i => old i
    have hDomain :
        Function.Injective root ∧
          (A.func p.input.symbol (root ∘ p.input.argMap)).Nonempty := by
      have hd : (A.patternGraph).rel (.inr (.inl p.input)) (old ∘ id) :=
        (old.map_rel_iff (.inr (.inl p.input)) id).mpr p.hasDomain
      exact hd
    obtain ⟨hinj, y, hy⟩ := hDomain
    let xs : Fin (p.input.rootSize + 1) → V :=
      Structure.funcTuple root y
    have hTag :
        (patternTagExpansion A.patternGraph).rel (.inr p) xs := by
      change (A.patternGraph).rel (.inr (.inr p.input)) xs ∧
        ∃ g : Embedding p.root A.patternGraph,
          ∀ i : Fin p.input.rootSize, xs i.castSucc = g i
      constructor
      · change Function.Injective (fun i => xs i.castSucc) ∧
          xs (Fin.last p.input.rootSize) ∈
            A.func p.input.symbol
              ((fun i => xs i.castSucc) ∘ p.input.argMap)
        simpa only [xs, Structure.funcTuple_castSucc,
          Structure.funcTuple_last] using
          (show Function.Injective root ∧
              y ∈ A.func p.input.symbol
                (root ∘ p.input.argMap) from ⟨hinj, hy⟩)
      · refine ⟨old, ?_⟩
        intro i
        rfl
    have hPrefix :
        ∀ i : Fin p.input.rootSize,
          xs i.castSucc = e i := by
      intro i
      rfl
    refine ⟨xs, ⟨hTag, hPrefix⟩, ?_⟩
    intro ys hyValid
    have hPrefixY :
        ∀ i : Fin p.input.rootSize,
          ys i.castSucc = root i := by
      intro i
      exact hyValid.2 i
    have hOutput :
        ys (Fin.last p.input.rootSize) ∈
          A.func p.input.symbol (root ∘ p.input.argMap) := by
      have hOld : (A.patternGraph).rel
          (.inr (.inr p.input)) ys := hyValid.1.1
      change
        Function.Injective (fun i => ys i.castSucc) ∧
        ys (Fin.last p.input.rootSize) ∈
          A.func p.input.symbol
            ((fun i => ys i.castSucc) ∘ p.input.argMap) at hOld
      have hEq :
          (fun i : Fin p.input.rootSize => ys i.castSucc) = root := by
        funext i
        exact hPrefixY i
      rw [hEq] at hOld
      exact hOld.2
    have hLast : ys (Fin.last p.input.rootSize) = y :=
      hA p.input.symbol (root ∘ p.input.argMap)
        _ _ hOutput hy
    apply funext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [xs, Structure.funcTuple_last] using hLast
    · simpa only [xs, Structure.funcTuple_castSucc] using hPrefixY j

end StructuralRamsey.RelStructure
