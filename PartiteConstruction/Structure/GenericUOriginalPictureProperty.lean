import PartiteConstruction.Structure.GenericUPictureProjected
import PartiteConstruction.Structure.GenericUGraphWitnessRoundtripClosed

/-!
# Track F — exact original-language Picture property transported from graph witnesses

The source is an arbitrary original relational (L,U) with positive U-output
arity. The graph Picture property colours genuinely function-closed,
projection-preserving A-copies in an arbitrary graph-language target.
Our target is its literal same-vertex, same-part decoded original system,
not an abstract isomorphic witness.

The inverse closed graph identity from GenericUGraphWitnessRoundtripClosed
and the original projected-copy equivalence from GenericUPictureProjected
transport the entire colouring and B-copy composition square.
-/

namespace StructuralRamsey.Partite.OriginalUClosed

universe u v
variable {L : RelLanguage.{u}} {P T V W : Type v}

/-- Literal arbitrary-(L,U) Picture property on the original relational
language: colour U-closed A-copies with fixed projection alpha and find a
U-closed partite B-copy making all its projected A-subcopies monochromatic. -/
def PictureProperty
    (A : RelStructure L T)
    (B : Partite.System L P V)
    (α : T → P)
    (C : Partite.System L P W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*) : Prop :=
  ∀ χ : ProjectedEmbedding A C α U hU → κ,
    ∃ f : Embedding B C U hU,
      ∀ e₁ e₂ : ProjectedEmbedding A B α U hU,
        χ (ProjectedEmbedding.comp α U hU e₁ f) =
          χ (ProjectedEmbedding.comp α U hU e₂ f)

/-- Transport the FULL graph Picture-property colouring, selected closed
partite B-copy and its every projected-A-copy composition into arbitrary
original L. The graph witness C_g need not be a canonical encoding. -/
theorem pictureProperty_of_graph
    (A : RelStructure L T)
    (B : Partite.System L P V)
    (α : T → P)
    (C_g : Partite.System (L.withUFunctionsReduced U).graph P W)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (κ : Type*)
    (hP : Partite.Closed.PictureProperty
      (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU) α C_g κ) :
    PictureProperty A B α
      (Partite.System.fromReducedUGraph U hU C_g)
      U hU κ := by
  classical
  let C := Partite.System.fromReducedUGraph U hU C_g
  let A_g := A.asReducedUGraph U hU
  let B_g := B.asReducedUGraph U hU
  let C_back := C.asReducedUGraph U hU
  let EB := projectedEmbeddingEquiv A B α U hU
  let EC := projectedEmbeddingEquiv A C α U hU
  let RC := Partite.Closed.projectedRoundtripEquiv U hU A_g C_g α
  let FB := Partite.Embedding.uClosedReindexEquiv
    (A := B) (B := C) U hU
  let back := Partite.System.graphRoundtripClosedBackward U hU C_g
  intro χ
  let χ_g : Partite.Closed.ProjectedEmbedding A_g C_g α → κ :=
    fun e => χ (EC.symm (RC e))
  obtain ⟨f_g, hf_g⟩ := hP χ_g
  let f_back : Partite.Closed.Embedding B_g C_back :=
    Partite.Closed.Embedding.comp back f_g
  let f : Embedding B C U hU := FB.symm f_back
  refine ⟨f, ?_⟩
  intro e₁ e₂
  have hcomp (e : ProjectedEmbedding A B α U hU) :
      EC.symm (RC ((EB e).comp f_g)) =
        ProjectedEmbedding.comp α U hU e f := by
    apply Subtype.ext
    apply Subtype.ext
    apply RelStructure.Embedding.ext
    intro x
    rfl
  have hmono := hf_g (EB e₁) (EB e₂)
  change χ (EC.symm (RC ((EB e₁).comp f_g))) =
    χ (EC.symm (RC ((EB e₂).comp f_g))) at hmono
  rw [hcomp e₁, hcomp e₂] at hmono
  exact hmono

end StructuralRamsey.Partite.OriginalUClosed
