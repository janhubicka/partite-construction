import PartiteConstruction.Functional.RecursiveConstruction
import PartiteConstruction.Functional.ClosedPartite

/-! # Relevant cores for arbitrary projections

For a fixed ordinary projection alpha : A -> D and a D-partite stage S, keep
only vertices which occur in a U-closed A-copy with projection alpha.  This is
the analogue of the semi-closed core used in the classical closure partite
construction.

The basic inherited invariants are independent of the unresolved higher-arity
extension problem: induced partite subsystems remain partite over the same
base, U-transversality is inherited, and every relevant closed A-copy factors
as a closed embedding into the relevant core.
-/
namespace StructuralRamsey.Partite.RelevantCore

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {U P X : Type v}

/-- Arbitrary induced partite subsystems preserve the homomorphism-embedding
projection invariant. -/
theorem induce_isPartiteOver
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (hS : S.IsPartiteOver D)
    (T : Set X) :
    (S.induce T).IsPartiteOver D := by
  change
    (S.toRelStructure.induce T).IsHomomorphismEmbedding D
      (S.part ∘ Subtype.val)
  exact hS.comp
    (RelStructure.inclusion S.toRelStructure T).isHomomorphismEmbedding

/-- U-transversality is inherited by induced partite subsystems. -/
theorem induce_uTransversal
    (S : Partite.System L.graph P X)
    (hS : S.FunctionOutputTransversal)
    (T : Set X) :
    (S.induce T).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  apply Subtype.ext
  exact hS F
    (Subtype.val ∘ x) y.1 z.1 hy hz hp

/-- A closed projected A-copy restricted to the alpha-parts.  Closedness of
alpha in D is not needed; closedness of the A-copy itself is enough. -/
def restrictProjected
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (e : Partite.Closed.ProjectedEmbedding A S α) :
    Partite.Closed.Embedding
      (Partite.transversal A)
      (S.restrict α.toFunctionEmbedding) := by
  let αf := α.toFunctionEmbedding
  let pe : Partite.Embedding
      (Partite.transversal A) (S.restrict αf) := {
    toFun := fun a => ⟨e.1 a, a, (e.2 a).symm⟩
    injective := by
      intro a b hab
      exact e.1.toEmbedding.injective
        (congrArg Subtype.val hab)
    map_rel_iff := by
      intro R x
      exact e.1.toEmbedding.map_rel_iff R x
    map_part := by
      intro a
      apply α.injective
      exact
        (S.restrictedPart_spec αf
          ⟨e.1 a, a, (e.2 a).symm⟩).trans (e.2 a)
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hyS :
      S.rel (.inr F)
        (Structure.funcTuple (e.1 ∘ x) y.1) := by
    change
      S.rel (.inr F)
        (Subtype.val ∘
          Structure.funcTuple (pe ∘ x) y) at hy
    have ht :
        Subtype.val ∘ Structure.funcTuple (pe ∘ x) y =
          Structure.funcTuple (e.1 ∘ x) y.1 := by
      exact Structure.comp_funcTuple
        Subtype.val (pe ∘ x) y
    rw [ht] at hy
    exact hy
  obtain ⟨a, ha, hay⟩ := e.1.closed F x y.1 hyS
  refine ⟨a, ha, ?_⟩
  apply Subtype.ext
  exact hay

/-- Vertices of the alpha-restriction which occur in some closed projected
A-copy. -/
def RelevantSet
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D) :
    Set (S.support α.toFunctionEmbedding) :=
  {x | ∃ e : Partite.Closed.ProjectedEmbedding A S α,
      ∃ a : U, e.1 a = x.1}

/-- The relevant core over alpha. -/
noncomputable def core
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D) :
    Partite.System L.graph U (RelevantSet S α) :=
  (S.restrict α.toFunctionEmbedding).induce (RelevantSet S α)

/-- The relevant core remains A-partite whenever S is D-partite. -/
theorem core_isPartiteOver
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (hS : S.IsPartiteOver D)
    (α : RelStructure.Embedding A D) :
    (core S α).IsPartiteOver A := by
  let R := S.restrict α.toFunctionEmbedding
  have hR : R.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver
      D S A hS α
  exact induce_isPartiteOver R hR (RelevantSet S α)

/-- The relevant core inherits U-transversality. -/
theorem core_uTransversal
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (hS : S.FunctionOutputTransversal)
    (α : RelStructure.Embedding A D) :
    (core S α).FunctionOutputTransversal := by
  let R := S.restrict α.toFunctionEmbedding
  have hR : R.FunctionOutputTransversal := by
    intro F x y z hy hz hp
    apply Subtype.ext
    exact hS F
      (Subtype.val ∘ x) y.1 z.1 hy hz
      (congrArg α.toFunctionEmbedding hp)
  exact induce_uTransversal R hR (RelevantSet S α)

/-- Every closed projected A-copy factors as a closed embedding into the
relevant core. -/
noncomputable def factorProjected
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (e : Partite.Closed.ProjectedEmbedding A S α) :
    Partite.Closed.Embedding (Partite.transversal A) (core S α) := by
  let r := restrictProjected S α e
  let f : U → RelevantSet S α := fun a =>
    ⟨r a, ⟨e, a, rfl⟩⟩
  let pe : Partite.Embedding (Partite.transversal A) (core S α) := {
    toFun := f
    injective := by
      intro a b hab
      apply r.1.injective
      exact congrArg Subtype.val hab
    map_rel_iff := by
      intro R x
      change
        (S.restrict α.toFunctionEmbedding).rel R
          (Subtype.val ∘ (f ∘ x)) ↔ A.rel R x
      convert r.1.map_rel_iff R x using 1
      funext i
      rfl
    map_part := by
      intro a
      exact r.1.map_part a
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hyR :
      (S.restrict α.toFunctionEmbedding).rel (.inr F)
        (Structure.funcTuple (r ∘ x) y.1.1) := by
    change
      (S.restrict α.toFunctionEmbedding).rel (.inr F)
        (Subtype.val ∘
          Structure.funcTuple (f ∘ x) y) at hy
    have ht :
        Subtype.val ∘ Structure.funcTuple (f ∘ x) y =
          Structure.funcTuple (r ∘ x) y.1.1 := by
      exact Structure.comp_funcTuple
        Subtype.val (f ∘ x) y
    rw [ht] at hy
    exact hy
  obtain ⟨a, ha, hay⟩ := r.2 F x y.1.1 hyR
  refine ⟨a, ha, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hay

/-- Every vertex of the relevant core lies in one of its factored closed
A-copies. -/
theorem vertex_covered
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (x : RelevantSet S α) :
    ∃ e : Partite.Closed.Embedding (Partite.transversal A) (core S α),
      ∃ a : U, e a = x := by
  rcases x.2 with ⟨e, a, hea⟩
  refine ⟨factorProjected S α e, a, ?_⟩
  apply Subtype.ext
  exact hea


/-- The same relevant vertices, viewed in the ambient carrier. -/
def AmbientRelevantSet
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D) :
    Set X :=
  {x | ∃ e : Partite.Closed.ProjectedEmbedding A S α,
      ∃ a : U, e.1 a = x}

/-- With unary functions, the union of all relevant closed A-copies is itself
function-closed.  Thus the genuine obstruction to using this relevant core
starts with higher-arity functions, where inputs may come from different
A-copies. -/
theorem ambientRelevant_functionClosed_unary
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (hUnary : ∀ F, L.funcArity F = 1) :
    RelStructure.FunctionClosedSet S.toRelStructure
      (AmbientRelevantSet S α) := by
  intro F x y hy hx
  have hpos : 0 < L.funcArity F := by
    rw [hUnary F]
    exact Nat.zero_lt_one
  let i0 : Fin (L.funcArity F) := ⟨0, hpos⟩
  obtain ⟨e, a, hea⟩ := hx i0
  let xa : Fin (L.funcArity F) → U := fun _ => a
  have hargs : e.1 ∘ xa = x := by
    funext i
    have hi : i = i0 := by
      rw [hUnary F] at i i0
      exact Subsingleton.elim _ _
    subst i
    exact hea
  have hy' :
      S.rel (.inr F)
        (Structure.funcTuple (e.1 ∘ xa) y) := by
    rw [hargs]
    exact hy
  obtain ⟨z, hz, hzy⟩ := e.1.closed F xa y hy'
  exact ⟨e, z, hzy⟩

/-- In the unary-function case the relevant core includes into the ambient
stage by a closed embedding. -/
noncomputable def coreInclusionClosed_unary
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (hUnary : ∀ F, L.funcArity F = 1) :
    RelStructure.ClosedEmbedding
      (core S α).toRelStructure S.toRelStructure := by
  let toAmbient : RelevantSet S α → X := fun x => x.1.1
  let emb : RelStructure.Embedding
      (core S α).toRelStructure S.toRelStructure := {
    toFun := toAmbient
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    map_rel_iff := by
      intro R x
      rfl
  }
  refine ⟨emb, ?_⟩
  intro F x y hy
  have hxRel : ∀ i, toAmbient (x i) ∈ AmbientRelevantSet S α := by
    intro i
    exact (x i).2
  have hyRel : y ∈ AmbientRelevantSet S α :=
    ambientRelevant_functionClosed_unary S α hUnary
      F (toAmbient ∘ x) y hy hxRel
  rcases hyRel with ⟨e, a, hea⟩
  have hSupport : y ∈ S.support α.toFunctionEmbedding := by
    exact ⟨a, (e.2 a).symm.trans (congrArg S.part hea)⟩
  let ys : S.support α.toFunctionEmbedding := ⟨y, hSupport⟩
  have hRelevant : ys ∈ RelevantSet S α := by
    exact ⟨e, a, hea⟩
  let z : RelevantSet S α := ⟨ys, hRelevant⟩
  refine ⟨z, ?_, ?_⟩
  · change
      (S.restrict α.toFunctionEmbedding).rel (.inr F)
        (Subtype.val ∘
          Structure.funcTuple x z)
    change
      S.rel (.inr F)
        (Subtype.val ∘
          (Subtype.val ∘ Structure.funcTuple x z))
    have ht :
        Subtype.val ∘
            (Subtype.val ∘ Structure.funcTuple x z) =
          Structure.funcTuple (toAmbient ∘ x) y := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rfl
    rw [ht]
    exact hy
  · rfl

end StructuralRamsey.Partite.RelevantCore
