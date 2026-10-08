import PartiteConstruction.Ramsey.ClosureDescription2019
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Images of embeddings preserve relational U-closedness

A full embedding of a U-closed structure into a U-closed structure has
U-closed image: whenever the input root of a closure relation tuple
lies in the image, its whole closure tuple already lies in the image.

This is stronger than the statement that the source is itself U-closed.
It is also the precise hypothesis needed when two U-closed structures
are freely amalgamated along a common full U-closed substructure.

We never assert this property for an EHN *weak* projection, and never
replace a weak image by its generated closure. -/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {U V : Type v}

/-- Factor an embedding through the closed range of another embedding,
allowing the source root to live in a different universe. This is
necessary for arbitrary finite root carriers `Fin n : Type 0` when
ambient structures live in `Type v`. -/
noncomputable def Embedding.factorThroughRangeHeterogeneous
    {X : Type w} {Root : RelStructure L X}
    {A : RelStructure L U} {B : RelStructure L V}
    (e : Embedding Root B) (i : Embedding A B)
    (h : ∀ x : X, ∃ a : U, e x = i a) :
    Embedding Root A where
  toFun := fun x => Classical.choose (h x)
  injective := by
    intro x y hxy
    apply e.injective
    calc
      e x = i (Classical.choose (h x)) := Classical.choose_spec (h x)
      _ = i (Classical.choose (h y)) := congrArg i hxy
      _ = e y := (Classical.choose_spec (h y)).symm
  map_rel_iff := by
    intro R xs
    let q : X → U := fun x => Classical.choose (h x)
    have heq : i ∘ (q ∘ xs) = e ∘ xs := by
      funext k
      exact (Classical.choose_spec (h (xs k))).symm
    calc
      A.rel R (q ∘ xs) ↔ B.rel R (i ∘ (q ∘ xs)) :=
        (i.map_rel_iff R (q ∘ xs)).symm
      _ ↔ B.rel R (e ∘ xs) := by rw [heq]
      _ ↔ Root.rel R xs := e.map_rel_iff R xs

/-- The image of a full embedding between U-closed relational
structures is a vertex-exact U-substructure. The proof only uses
embedding-domain reflection and uniqueness of each root's closure
tuple, not root irreducibility. -/
theorem Embedding.range_isUSubstructure
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (hA : IsUClosed rules A)
    (hB : IsUClosed rules B)
    (e : Embedding A B) :
    IsUSubstructure rules B (Set.range e) := by
  classical
  intro rule hrule t ht hRootRange j
  obtain ⟨rootB,hRootB⟩ := (hB rule hrule).1 t ht
  have hrange : ∀ i : Fin rule.rootSize, ∃ a : U,
      rootB i = e a := by
    intro i
    obtain ⟨a,ha⟩ := hRootRange i
    exact ⟨a, (hRootB i).symm.trans ha.symm⟩
  let rootA : Embedding rule.root A :=
    rootB.factorThroughRangeHeterogeneous e hrange
  have hrootA (i : Fin rule.rootSize) :
      rootB i = e (rootA i) :=
    Classical.choose_spec (hrange i)
  obtain ⟨tA,htA,_hUniqueA⟩ := (hA rule hrule).2 rootA
  have htB : B.rel rule.symbol (e ∘ tA) :=
    (e.map_rel_iff rule.symbol tA).mpr htA.1
  have hRootImage : ∀ i : Fin rule.rootSize,
      (e ∘ tA) (i.castLE rule.rootLE) = rootB i := by
    intro i
    change e (tA (i.castLE rule.rootLE)) = rootB i
    rw [htA.2 i]
    exact (hrootA i).symm
  obtain ⟨q,hq,hUniqueB⟩ := (hB rule hrule).2 rootB
  have htq : t = q := hUniqueB t ⟨ht,hRootB⟩
  have heq : (e ∘ tA) = q :=
    hUniqueB (e ∘ tA) ⟨htB,hRootImage⟩
  have hte : t = e ∘ tA := htq.trans heq.symm
  rw [hte]
  exact ⟨tA j,rfl⟩

/-- Equivalently, an embedded U-closed structure occupies a
U-closed induced vertex set in a U-closed target. -/
theorem Embedding.range_induce_isUClosed
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (hA : IsUClosed rules A)
    (hB : IsUClosed rules B)
    (e : Embedding A B) :
    IsUClosed rules (B.induce (Set.range e)) :=
  hB.induce_of_USubstructure (Set.range e)
    (e.range_isUSubstructure hA hB)

end StructuralRamsey.RelStructure
