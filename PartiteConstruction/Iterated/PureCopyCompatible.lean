import PartiteConstruction.Iterated.PartialCompatibleLocalTreeLike
import PartiteConstruction.Partite.InducedPicture

/-! # Partial-A-compatible witnesses in the pure-copy case

If a tested set in one Picture step lies wholly in one attached old copy, the
whole tested induced structure pulls back by an induced embedding into the old
stage.  More importantly, every induced partial A-copy whose image lies in the
test pulls back through the same copy embedding.

Thus the partial-A compatibility invariant is inherited verbatim from the old
stage.  No hereditary irreducibility is used.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- A test contained in one attached copy inherits a partial-compatible tree
witness from the old stage. -/
theorem pureCopy_partialWitness
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (E : Partite.System L U Y)
    (n : ℕ)
    (hOld :
      RelStructure.PartialCompatibleLocallyTreeLike
        (A := A) B C₀.toRelStructure n)
    (i : Partite.Embedding (C₀.restrict α.toFunctionEmbedding) E)
    (Test : Finset (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E))
    (hTestCard : Test.card ≤ n)
    (hcopy :
      ∀ z : ↥(↑Test :
          Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E)),
        RelStructure.Attachment.InCopy
          C₀.toRelStructure (C₀.support α.toFunctionEmbedding)
          (E.relabel α.toFunctionEmbedding).toRelStructure
          (fun j =>
            (Partite.Picture.attachingMap
              C₀ α.toFunctionEmbedding E j).toEmbedding)
          i z.1) :
    let C₁ := Partite.Picture.build C₀ α.toFunctionEmbedding E
    let TestSet : Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E) :=
      ↑Test
    let Small := C₁.toRelStructure.induce TestSet
    ∃ (Z : Type v) (Target : RelStructure L Z),
      TreeAmalgam B Z Target ∧
      ∃ f : ↥TestSet → Z,
        Small.IsHomomorphismEmbedding Target f ∧
        RelStructure.PartialEmbeddedIntersections
          (A := A) (C := C₁.toRelStructure) (T := Target) Test f := by
  classical
  let αf := α.toFunctionEmbedding
  let C₁ := Partite.Picture.build C₀ αf E
  let Tset : Set (Partite.Picture.Vertex C₀ αf E) := ↑Test
  let Small := C₁.toRelStructure.induce Tset
  let smallIncl : RelStructure.Embedding Small C₁.toRelStructure :=
    RelStructure.inclusion C₁.toRelStructure Tset
  have hrange :
      ∀ z : Tset, ∃ x : X,
        smallIncl z =
          (Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding x := by
    intro z
    rcases hcopy z with ⟨x, hx⟩
    exact ⟨x, hx⟩
  let eCopy : RelStructure.Embedding Small C₀.toRelStructure :=
    smallIncl.factorThroughRange
      (Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding hrange
  have hSmall :
      RelStructure.PartialCompatibleLocallyTreeLike
        (A := A) B Small n :=
    hOld.pullback_embedding eCopy

  letI : Fintype Tset := Fintype.ofFinite Tset
  have hcard :
      (Finset.univ : Finset Tset).card ≤ n := by
    simpa [Tset] using hTestCard
  obtain ⟨Z, Target, hTree, f₀, hf₀, hPartial₀⟩ :=
    hSmall (Finset.univ : Finset Tset) hcard

  let allEmb :
      RelStructure.Embedding Small
        (Small.induce (↑(Finset.univ : Finset Tset) : Set Tset)) := {
    toFun := fun z => ⟨z, Finset.mem_univ z⟩
    injective := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let f : Tset → Z := f₀ ∘ allEmb
  have hf : Small.IsHomomorphismEmbedding Target f :=
    hf₀.comp allEmb.isHomomorphismEmbedding

  refine ⟨Z, Target, hTree, f, hf, ?_⟩
  intro H q hRange
  let qSmall : RelStructure.Embedding (A.induce H) Small := {
    toFun := fun x => ⟨q x, hRange x⟩
    injective := by
      intro x y hxy
      apply q.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change C₁.toRelStructure.rel R (q ∘ x) ↔
        A.rel R (Subtype.val ∘ x)
      exact q.map_rel_iff R x
  }
  have hRangeUniv :
      ∀ x, qSmall x ∈ (Finset.univ : Finset Tset) :=
    fun x => Finset.mem_univ _
  obtain ⟨qT, hqT, hc⟩ :=
    hPartial₀ H qSmall hRangeUniv
  refine ⟨qT, ?_, hc⟩
  intro x
  change qT x = f₀ (allEmb ⟨q x, hRange x⟩)
  exact hqT x

end StructuralRamsey.Partite.Iterated
