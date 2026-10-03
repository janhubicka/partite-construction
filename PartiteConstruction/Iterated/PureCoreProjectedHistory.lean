import PartiteConstruction.Iterated.ProjectedHistoryLocalTreeLike
import PartiteConstruction.Iterated.PureCoreProjectedCompatible

/-! # Projected histories in the pure-core case

The pure-core one-copy B witness from the projected-partial construction has a
stronger property: equality in the target B-copy forces equality of the
projected D-part.  Hence it respects every finite history of base subsets
without any additional construction.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- Pure-core witness carrying both projected partial intersections and an
arbitrary finite history. -/
theorem pureCore_projectedHistoryWitness
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (E : Partite.System L U Y)
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (hE : E.IsPartiteOver A)
    (Test : Finset (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E))
    (hcore :
      ∀ z : ↥(↑Test :
          Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E)),
        ∃ w : Y,
          z.1 =
            Partite.Picture.coreEmbedding
              C₀ α.toFunctionEmbedding E w)
    (history : List (Set P)) :
    let C₁ := Partite.Picture.build C₀ α.toFunctionEmbedding E
    let TestSet : Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E) :=
      ↑Test
    let Small := C₁.toRelStructure.induce TestSet
    ∃ f : ↥TestSet → V,
      Small.IsHomomorphismEmbedding B f ∧
      RelStructure.ProjectedPartialIntersections
        (A := A) (D := D) (C := C₁.toRelStructure) (T := B)
        C₁.part Test f ∧
      RelStructure.RespectsProjectedHistory
        C₁.part Test f history := by
  classical
  let αf := α.toFunctionEmbedding
  let Core := E.relabel αf
  let C₁ := Partite.Picture.build C₀ αf E
  let Tset : Set (Partite.Picture.Vertex C₀ αf E) := ↑Test
  let Small := C₁.toRelStructure.induce Tset
  let smallIncl : RelStructure.Embedding Small C₁.toRelStructure :=
    RelStructure.inclusion C₁.toRelStructure Tset
  let coreEmb : Partite.Embedding Core C₁ :=
    Partite.Picture.coreEmbedding C₀ αf E
  let eCore : RelStructure.Embedding Small Core.toRelStructure :=
    smallIncl.factorThroughRange coreEmb.toEmbedding hcore
  have heCore (z : Tset) :
      smallIncl z = coreEmb.toEmbedding (eCore z) :=
    Classical.choose_spec (hcore z)

  let toA : Tset → U := fun z => E.part (eCore z)
  have hToA : Small.IsHomomorphismEmbedding A toA := by
    change Small.IsHomomorphismEmbedding A (E.part ∘ eCore)
    have hCoreToA :
        Core.toRelStructure.IsHomomorphismEmbedding A E.part := by
      change E.toRelStructure.IsHomomorphismEmbedding A E.part
      exact hE
    exact hCoreToA.comp eCore.isHomomorphismEmbedding

  let f : Tset → V := fun z => eAB (toA z)
  have hf : Small.IsHomomorphismEmbedding B f := by
    change Small.IsHomomorphismEmbedding B (eAB ∘ toA)
    exact eAB.isHomomorphismEmbedding.comp hToA

  have hPartSpec (z : Tset) :
      C₁.part z.1 = α (toA z) := by
    calc
      C₁.part z.1 =
          C₁.part (coreEmb.toEmbedding (eCore z)) := by
            exact congrArg C₁.part (heCore z)
      _ = Core.part (eCore z) := coreEmb.map_part (eCore z)
      _ = α (E.part (eCore z)) := rfl
      _ = α (toA z) := rfl

  have hPart :
      RelStructure.ProjectedPartialIntersections
        (A := A) (D := D) (C := C₁.toRelStructure) (T := B)
        C₁.part Test f := by
    intro β H q hqproj hqRange
    let βH : RelStructure.Embedding (A.induce H) D :=
      β.comp (RelStructure.inclusion A H)
    have hRangeAlpha :
        ∀ x : H, ∃ a : U, βH x = α a := by
      intro x
      let z : Tset := ⟨q x, hqRange x⟩
      refine ⟨toA z, ?_⟩
      calc
        βH x = β x.1 := rfl
        _ = C₁.part (q x) := (hqproj x).symm
        _ = α (toA z) := hPartSpec z
    let eHA : RelStructure.Embedding (A.induce H) A :=
      βH.factorThroughRange α hRangeAlpha
    let eHB : RelStructure.Embedding (A.induce H) B :=
      eAB.comp eHA
    have heHB :
        ∀ x : H, eHB x = f ⟨q x, hqRange x⟩ := by
      intro x
      let z : Tset := ⟨q x, hqRange x⟩
      change eAB (eHA x) = eAB (toA z)
      apply congrArg eAB
      apply α.injective
      have hfactor : βH x = α (eHA x) :=
        Classical.choose_spec (hRangeAlpha x)
      calc
        α (eHA x) = βH x := hfactor.symm
        _ = β x.1 := rfl
        _ = C₁.part (q x) := (hqproj x).symm
        _ = α (toA z) := hPartSpec z
    have hcHB : eHB.ContainedInIrreducible := by
      apply RelStructure.Embedding.containedInIrreducible_of_range_subset
        hA eAB eHB
      intro x
      exact ⟨eHA x, rfl⟩
    exact ⟨eHB, heHB, hcHB⟩

  have hKernel :
      ∀ x y : Tset, f x = f y →
        C₁.part x.1 = C₁.part y.1 := by
    intro x y hxy
    have hAeq : toA x = toA y := by
      apply eAB.injective
      exact hxy
    rw [hPartSpec x, hPartSpec y, hAeq]

  have hHist :
      RelStructure.RespectsProjectedHistory
        C₁.part Test f history :=
    RelStructure.ProjectedHistoryLocallyTreeLike.
      respectsHistory_of_kernel_refines_projection
        (p := C₁.part) hKernel history

  exact ⟨f, hf, hPart, hHist⟩

end StructuralRamsey.Partite.Iterated
