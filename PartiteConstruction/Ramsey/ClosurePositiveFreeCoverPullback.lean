import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Ramsey.ClosureProjectedGenerators

/-!
# Pulling an exact free cover back through a POSITIVE map

The repaired closed-rank j->j+1 proof analyzes a U-closed test T
through a protected POSITIVE projection to a temporarily nonclosed
Hales--Jewett Picture O. This projection may identify unrelated
vertices, so it is invalid to treat it as a global embedding.

An important valid reduction needs only positivity:

* If the target structure has a two-sided exact free cover
  by sets S and R (every tuple is contained in one side),
  then the inverse-image sets f⁻¹(S), f⁻¹(R) form an exact
  free-amalgam decomposition of the source.
* If both target sides are RELATIVELY U-closed, both source
  sides are relatively U-closed by preimages under positive maps.
* If the source is intrinsically U-closed, its exact induced
  sides are intrinsically U-closed. No closure hull or additional
  vertices are introduced and the projection need NOT be
  injective or reflect absent relation tuples.
* A closed U-irreducible source has its WHOLE image on one side.

This is a conditional SOURCE-decomposition tool; it does not assert
the actual native attachment's chosen copy/rest side ranges are
relatively U-closed. Those must be checked from the history, and
the resulting side completion ranks may still fail to drop.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

variable {A : RelStructure L U} {B : RelStructure L V}
variable {f : U → V}

/-- A positive map pulls back a free cover of the target to an
actual free amalgam of the EXACT induced source pieces.
No source/target U-closedness or map injectivity is assumed. -/
theorem IsHomomorphism.pullback_free_cover
    (hf : A.IsHomomorphism B f)
    (S T : Set V)
    (hCover : ∀ y : V, y ∈ S ∨ y ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → V),
      B.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    let SL : Set U := f ⁻¹' S
    let SR : Set U := f ⁻¹' T
    let Root : Set U := SL ∩ SR
    IsFreeAmalgam
      (show Embedding (A.induce Root) (A.induce SL) from {
        toFun := fun x => ⟨x.1, x.2.1⟩
        injective := by
          intro x y h
          exact Subtype.ext (congrArg (fun z : SL => z.1) h)
        map_rel_iff := fun _ _ => Iff.rfl })
      (show Embedding (A.induce Root) (A.induce SR) from {
        toFun := fun x => ⟨x.1, x.2.2⟩
        injective := by
          intro x y h
          exact Subtype.ext (congrArg (fun z : SR => z.1) h)
        map_rel_iff := fun _ _ => Iff.rfl })
      (inclusion A SL) (inclusion A SR) := by
  dsimp
  constructor
  · intro x
    rcases hCover (f x) with hS | hT
    · exact Or.inl ⟨⟨x, hS⟩, rfl⟩
    · exact Or.inr ⟨⟨x, hT⟩, rfl⟩
  · intro a b
    constructor
    · intro hab
      have heq : a.1 = b.1 := hab
      have hRight : f a.1 ∈ T := by
        rw [heq]
        exact b.2
      exact ⟨⟨a.1, a.2, hRight⟩,
        Subtype.ext rfl, Subtype.ext heq.symm⟩
    · rintro ⟨d, rfl, rfl⟩
      rfl
  · intro R z
    constructor
    · intro hz
      rcases hTuples R (f ∘ z) (hf R z hz) with hS | hT
      · exact Or.inl ⟨(fun k => ⟨z k, hS k⟩), hz, rfl⟩
      · exact Or.inr ⟨(fun k => ⟨z k, hT k⟩), hz, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ha
      · exact hb

/-- Relatively U-closed target sides remain relatively closed after
pullback along a POSITIVE map. If A is U-closed, BOTH exact induced
preimage sides are intrinsically U-closed as well. -/
theorem IsHomomorphism.pullback_closed_sides
    {rules : ClosureDescription L}
    (hf : A.IsHomomorphism B f)
    (S T : Set V)
    (hS : IsUSubstructure rules B S)
    (hT : IsUSubstructure rules B T) :
    IsUSubstructure rules A (f ⁻¹' S) ∧
    IsUSubstructure rules A (f ⁻¹' T) := by
  exact ⟨hS.preimage_homomorphism hf,
    hT.preimage_homomorphism hf⟩

/-- A U-closed source can be split into CLOSED induced free pieces
using any relatively closed free cover of the target and a
POSITIVE map, without requiring that the map is a global
homomorphism-embedding or the target itself is U-closed. -/
theorem IsHomomorphism.pullback_closed_free_pieces
    {rules : ClosureDescription L}
    (hf : A.IsHomomorphism B f)
    (hA : IsUClosed rules A)
    (S T : Set V)
    (hS : IsUSubstructure rules B S)
    (hT : IsUSubstructure rules B T)
    (hCover : ∀ y : V, y ∈ S ∨ y ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → V),
      B.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    IsUClosed rules (A.induce (f ⁻¹' S)) ∧
    IsUClosed rules (A.induce (f ⁻¹' T)) := by
  obtain ⟨hLeft, hRight⟩ := hf.pullback_closed_sides S T hS hT
  exact ⟨hA.induce_of_USubstructure (f ⁻¹' S) hLeft,
    hA.induce_of_USubstructure (f ⁻¹' T) hRight⟩

/-- A protected CLOSED U-irreducible source cannot project to
both exclusive sides of a relatively U-closed free target cover.
Positivity of the projection suffices; no injectivity or tuple
reflection of f is needed. -/
theorem IsUIrreducible.positive_image_in_one_free_side
    {rules : ClosureDescription L}
    (hIrred : IsUIrreducible rules A)
    (hClosed : IsUClosed rules A)
    (hf : A.IsHomomorphism B f)
    (S T : Set V)
    (hS : IsUSubstructure rules B S)
    (hT : IsUSubstructure rules B T)
    (hCover : ∀ y : V, y ∈ S ∨ y ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → V),
      B.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    (∀ x : U, f x ∈ S) ∨ (∀ x : U, f x ∈ T) := by
  obtain ⟨hLeft, hRight⟩ :=
    hf.pullback_closed_sides S T hS hT
  have hCov : ∀ x : U, x ∈ f ⁻¹' S ∨ x ∈ f ⁻¹' T :=
    fun x => hCover (f x)
  have hTup : ∀ R (z : Fin (L.arity R) → U), A.rel R z →
      (∀ k, z k ∈ f ⁻¹' S) ∨ (∀ k, z k ∈ f ⁻¹' T) := by
    intro R z hz
    exact hTuples R (f ∘ z) (hf R z hz)
  exact hIrred.closed_cover hClosed (f ⁻¹' S) (f ⁻¹' T)
    hLeft hRight hCov hTup

end StructuralRamsey.RelStructure
