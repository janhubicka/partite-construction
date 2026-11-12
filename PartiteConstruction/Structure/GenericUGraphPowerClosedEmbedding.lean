import PartiteConstruction.Structure.GenericUGraphPower
import PartiteConstruction.Functional.ClosedPartite

/-!
# Track F — closed embedding of the genuine coordinate powers

The survey's induced partite lemma names the ACTUAL original power B^N.
The already-checked function-graph lemma produces the power of the
graph-language representation. The two concrete tagged power types are
equivalent by their unchanged parts and coordinates.

This module gives the reverse power map a genuine part-preserving induced
embedding, and shows it is closed for every graph-function output simply
because it is surjective. It is not a replacement for the actual B^N.

A generic monotonicity theorem carries the full graph closed-partite
Ramsey arrow along any such closed target embedding.
-/

namespace StructuralRamsey.Partite
universe u v

variable {L : RelLanguage.{u}} {P V : Type v}

/-- The reverse tagged-vertex equivalence preserves the exact induced
coordinatewise relation, part map, and all tuple coordinates. -/
noncomputable def fromGraphPower
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ) :
    Partite.Embedding
      (Induced.power (B.asReducedUGraph U hU) N)
      ((Induced.power B N).asReducedUGraph U hU) where
  toFun := (NonInduced.Vertex.uGraphEquiv B U hU N).symm
  injective :=
    (NonInduced.Vertex.uGraphEquiv B U hU N).symm.injective
  map_rel_iff := by
    intro S t
    let E := NonInduced.Vertex.uGraphEquiv B U hU N
    have hrel := Induced.power_reindex_rel_iff
      B U hU N S (fun i => E.symm (t i))
    have hfix :
        (fun i => (NonInduced.Vertex.uGraphEquiv B U hU N)
          (E.symm (t i))) = t := by
      funext i
      exact E.apply_symm_apply (t i)
    rw [hfix] at hrel
    exact hrel
  map_part := by
    intro x
    rfl

@[simp] theorem fromGraphPower_apply
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ)
    (x : NonInduced.Vertex (B.asReducedUGraph U hU) N) :
    fromGraphPower B U hU N x =
      (NonInduced.Vertex.uGraphEquiv B U hU N).symm x := rfl

namespace Closed

variable {K : Language.{u}}
variable {Q X Y : Type v}

/-- Any SURJECTIVE induced partite embedding of graph structures has
exact output-fibre lifting, hence is closed, with no cardinality or
total/singleton-function premise. -/
noncomputable def ofSurjectivePartite
    {A : Partite.System K.graph Q X}
    {B : Partite.System K.graph Q Y}
    (e : Partite.Embedding A B)
    (hsurj : Function.Surjective e.toEmbedding.toFun) :
    Embedding A B := by
  refine ⟨e, ?_⟩
  intro F x y hy
  obtain ⟨z, rfl⟩ := hsurj y
  refine ⟨z, ?_, rfl⟩
  have htarget : B.rel (.inr F)
      (e.toEmbedding.toFun ∘ Structure.funcTuple x z) := by
    have htuple := Structure.comp_funcTuple e.toEmbedding.toFun x z
    exact Eq.mp (congrArg (fun q => B.rel (.inr F) q) htuple.symm) hy
  exact (e.toEmbedding.map_rel_iff (.inr F)
    (Structure.funcTuple x z)).mp htarget

/-- A closed partite Ramsey arrow persists under a closed embedding of
its TARGET, using literal composition of all embeddings and colourings. -/
theorem arrow_of_closed_target
    {A : Partite.System K.graph Q X}
    {B : Partite.System K.graph Q Y}
    {Z T : Type v}
    {C : Partite.System K.graph Q Z}
    {D : Partite.System K.graph Q T}
    (i : Embedding C D)
    (κ : Type*)
    (h : Arrow A B C κ) : Arrow A B D κ := by
  intro χ
  let χC : Embedding A C → κ :=
    fun e => χ (Embedding.comp i e)
  obtain ⟨f, hf⟩ := h χC
  refine ⟨Embedding.comp i f, ?_⟩
  intro e₁ e₂
  have hc (e : Embedding A B) :
      Embedding.comp (Embedding.comp i f) e =
        Embedding.comp i (Embedding.comp f e) := by
    apply Embedding.ext
    intro x
    rfl
  have hχ := hf e₁ e₂
  change χ (Embedding.comp i (Embedding.comp f e₁)) =
    χ (Embedding.comp i (Embedding.comp f e₂)) at hχ
  simpa only [hc] using hχ

end Closed

/-- An exact graph-power Ramsey witness embeds CLOSEDLY into the reindexed
actual original power, on the inverse tagged-vertex equivalence. -/
noncomputable def closedFromGraphPower
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (N : ℕ) :
    Closed.Embedding
      (Induced.power (B.asReducedUGraph U hU) N)
      ((Induced.power B N).asReducedUGraph U hU) := by
  let e := fromGraphPower B U hU N
  have hsurj : Function.Surjective e.toEmbedding.toFun := by
    intro x
    refine ⟨NonInduced.Vertex.uGraphEquiv B U hU N x, ?_⟩
    exact (NonInduced.Vertex.uGraphEquiv B U hU N).symm_apply_apply x
  exact Closed.ofSurjectivePartite e hsurj

end StructuralRamsey.Partite
