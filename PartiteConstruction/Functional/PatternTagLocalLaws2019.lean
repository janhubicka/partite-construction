import PartiteConstruction.Functional.PatternClosureCanonical2019

/-!
# Local normality and graph-root validity of fresh 2019 closure tags

A tagged structure can be U-closed without faithfully encoding its
original function graph: an old graph tuple may be inconsistent with
the domain relation, and a fresh tag may be missing or spurious.

Two essential local laws are isolated independently:
* tag normality: each fresh closure relation equals its canonical
  interpretation from the OLD full induced root pattern;
* output-root validity: every old output tuple has a matching true
  domain relation on the exact distinct-input prefix.

Canonical primitive structures satisfy both laws; both laws transfer
backward along a FULL tagged embedding, without enlarging root vertices.

These results are separate from cross-pattern compatibility: different
equality-pattern representations of the same primitive argument tuple
must still be shown to give the same domain and output.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v w
variable {L : Language.{u}}

/-- A new closure tag means exactly its canonical old graph tuple
and complete FULL old root pattern, no more and no less. -/
def PatternTagNormal {V : Type v}
    (E : RelStructure (L.patternTag) V) : Prop :=
  ∀ (p : Language.FunctionRootPattern L)
    (xs : Fin (p.input.rootSize + 1) → V),
      E.rel (.inr p) xs ↔
      (patternTagExpansion (patternTagReduct E)).rel (.inr p) xs

/-- Every OLD function-output graph tuple has its corresponding OLD
active domain root. Root vertices remain exactly the prefix of the
tuple, and each root represents a distinct input vertex. -/
def PatternTagGraphRootValid {V : Type v}
    (E : RelStructure (L.patternTag) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (t : Fin (p.rootSize + 1) → V),
      (patternTagReduct E).rel (.inr (.inr p)) t →
      (patternTagReduct E).rel (.inr (.inl p))
        (fun i : Fin p.rootSize => t i.castSucc)

/-- Every canonical tag expansion is normal, with no closure assumption. -/
theorem patternTag_normal_canonical {V : Type v}
    (E : RelStructure (L.patternGraph) V) :
    PatternTagNormal (patternTagExpansion E) := by
  intro p xs
  rfl

/-- The canonical OLD encoding of a native set-valued function
structure always records its domain whenever it records an output. -/
theorem patternTag_valid_canonical {V : Type v}
    (A : Structure L V) :
    PatternTagGraphRootValid (patternTagExpansion A.patternGraph) := by
  intro p xs hOld
  change
    Function.Injective (fun i : Fin p.rootSize => xs i.castSucc) ∧
    xs (Fin.last p.rootSize) ∈ A.func p.symbol
      ((fun i : Fin p.rootSize => xs i.castSucc) ∘ p.argMap) at hOld
  change
    Function.Injective (fun i : Fin p.rootSize => xs i.castSucc) ∧
    (A.func p.symbol
      ((fun i : Fin p.rootSize => xs i.castSucc) ∘ p.argMap)).Nonempty
  exact ⟨hOld.1, ⟨xs (Fin.last p.rootSize), hOld.2⟩⟩

/-- A full tagged embedding reflects normality from its target.
The full OLD root pattern must be reflected, not merely the output
relation; this uses the already verified canonical tag embedding. -/
theorem PatternTagNormal.of_embedding
    {V : Type v} {W : Type w}
    {A : RelStructure (L.patternTag) V}
    {B : RelStructure (L.patternTag) W}
    (f : Embedding A B) (hB : PatternTagNormal B) :
    PatternTagNormal A := by
  intro p xs
  let fOld : Embedding (patternTagReduct A) (patternTagReduct B) :=
    f.patternTagReduct
  have hfTag : Embedding
      (patternTagExpansion (patternTagReduct A))
      (patternTagExpansion (patternTagReduct B)) :=
    fOld.patternTag
  calc
    A.rel (.inr p) xs ↔ B.rel (.inr p) (f ∘ xs) :=
      (f.map_rel_iff (.inr p) xs).symm
    _ ↔ (patternTagExpansion (patternTagReduct B)).rel
        (.inr p) (f ∘ xs) := hB p (f ∘ xs)
    _ ↔ (patternTagExpansion (patternTagReduct A)).rel
        (.inr p) xs := by
          have hFun : hfTag.toFun = f.toFun := by
            funext x
            dsimp [hfTag, fOld, Embedding.patternTag,
              Embedding.patternTagReduct]
          simpa only [hFun] using (hfTag.map_rel_iff (.inr p) xs)

/-- A full tagged embedding also reflects the old output-root
validity law. The exact input prefix is transported, unchanged in
cardinality, by the embedding of OLD reducts. -/
theorem PatternTagGraphRootValid.of_embedding
    {V : Type v} {W : Type w}
    {A : RelStructure (L.patternTag) V}
    {B : RelStructure (L.patternTag) W}
    (f : Embedding A B) (hB : PatternTagGraphRootValid B) :
    PatternTagGraphRootValid A := by
  intro p xs hOld
  let fOld : Embedding (patternTagReduct A) (patternTagReduct B) :=
    f.patternTagReduct
  have hBGraph :
      (patternTagReduct B).rel (.inr (.inr p))
        (fOld ∘ xs) :=
    (fOld.map_rel_iff (.inr (.inr p)) xs).mpr hOld
  have hBDomain := hB p (fOld ∘ xs) hBGraph
  have hBDomain' :
      (patternTagReduct B).rel (.inr (.inl p))
        (fOld ∘ (fun i : Fin p.rootSize => xs i.castSucc)) := by
    exact hBDomain
  exact (fOld.map_rel_iff (.inr (.inl p))
    (fun i : Fin p.rootSize => xs i.castSucc)).mp hBDomain'

end StructuralRamsey.RelStructure
