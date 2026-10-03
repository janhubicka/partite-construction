import PartiteConstruction.Iterated.ProjectedPartialLocalTreeLike
import PartiteConstruction.Iterated.AttachmentDecompose
import PartiteConstruction.Partite.InducedPicture

/-! # Projected partial compatibility in the pure-copy case

A tested set contained in one attached old copy pulls back into the previous
partite stage.  The old and new part projections agree along that copy, so
projection-compatible partial-A data is inherited verbatim.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- Pure-copy inheritance for the projection-history invariant. -/
theorem pureCopy_projectedPartialWitness
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (E : Partite.System L U Y)
    (n : ℕ)
    (hOld :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := C₀.toRelStructure)
        B C₀.part n)
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
        RelStructure.ProjectedPartialIntersections
          (A := A) (D := D) (C := C₁.toRelStructure) (T := Target)
          C₁.part Test f := by
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

  let pSmall : Tset → P := fun z => C₁.part z.1
  have hpSmall (z : Tset) :
      pSmall z = C₀.part (eCopy z) := by
    have hz :
        smallIncl z =
          (Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding (eCopy z) :=
      Classical.choose_spec (hrange z)
    change C₁.part z.1 = C₀.part (eCopy z)
    calc
      C₁.part z.1 =
          C₁.part
            ((Partite.Picture.copyEmbedding C₀ αf E i).toEmbedding
              (eCopy z)) := congrArg C₁.part hz
      _ = C₀.part (eCopy z) :=
        (Partite.Picture.copyEmbedding C₀ αf E i).map_part (eCopy z)

  have hSmall :
      RelStructure.ProjectedPartialLocallyTreeLike
        (A := A) (D := D) (C := Small)
        B pSmall n :=
    hOld.pullback_embedding eCopy hpSmall

  letI : Fintype Tset := Fintype.ofFinite Tset
  have hcard :
      (Finset.univ : Finset Tset).card ≤ n := by
    simpa [Tset] using hTestCard
  obtain ⟨Z, Target, hTree, f₀, hf₀, hPart₀⟩ :=
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
  intro β H q hqproj hqRange
  let qSmall : RelStructure.Embedding (A.induce H) Small := {
    toFun := fun x => ⟨q x, hqRange x⟩
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
  have hqprojSmall : ∀ x, pSmall (qSmall x) = β x.1 := by
    intro x
    exact hqproj x
  have hqRangeUniv :
      ∀ x, qSmall x ∈ (Finset.univ : Finset Tset) :=
    fun _ => Finset.mem_univ _
  obtain ⟨qT, hqT, hc⟩ :=
    hPart₀ β H qSmall hqprojSmall hqRangeUniv
  refine ⟨qT, ?_, hc⟩
  intro x
  change qT x = f₀ (allEmb ⟨q x, hqRange x⟩)
  exact hqT x

end StructuralRamsey.Partite.Iterated
