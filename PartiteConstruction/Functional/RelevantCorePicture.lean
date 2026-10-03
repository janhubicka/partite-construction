import PartiteConstruction.Functional.RelevantCore
import PartiteConstruction.Functional.ClosedAttachment
import PartiteConstruction.Partite.InducedAttachment

/-! # Unary relevant-core Picture construction

For unary function symbols, the union of all vertices occurring in relevant
closed A-copies is itself function-closed.  This permits the classical
relevant-core strategy even when the prescribed projection alpha : A -> D is
not closed:

1. pass to the U-partite relevant core;
2. apply the closed Hales--Jewett Partite Lemma there;
3. relabel the resulting power along alpha;
4. freely attach a copy of the whole current D-partite stage over every closed
   embedding of the relevant core into the power.

Because the ambient relevant subset is function-closed in the unary case, the
free attachment preserves closedness and U-transversality.  This yields the
previously missing local half-closed Picture witness for every ordinary alpha.
-/
namespace StructuralRamsey.Partite.RelevantCorePicture

open RelStructure Structure
open RelevantCore

universe u v
variable {L : Language.{u}}
variable {U P X : Type v}

/-- Relabelling a closed partite embedding preserves closedness because the
underlying relational structures do not change. -/
def relabelClosed
    {P Q V W : Type v}
    {A : Partite.System L.graph P V}
    {B : Partite.System L.graph P W}
    (e : Partite.Closed.Embedding A B)
    (ρ : P ↪ Q) :
    Partite.Closed.Embedding (A.relabel ρ) (B.relabel ρ) :=
  ⟨Partite.Embedding.relabel e.1 ρ, e.2⟩

/-- U-transversality is preserved by injective relabelling of parts. -/
theorem uTransversal_relabel
    {P Q V : Type v}
    (A : Partite.System L.graph P V)
    (ρ : P ↪ Q)
    (hA : A.FunctionOutputTransversal) :
    (A.relabel ρ).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  apply hA F x y z hy hz
  exact ρ.injective hp

/-- The relevant vertices directly as an induced subsystem of the ambient
D-partite stage. -/
def ambientCore
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D) :
    Partite.System L.graph P (AmbientRelevantSet S α) :=
  S.induce (AmbientRelevantSet S α)

/-- Repackage an ambient relevant vertex as a vertex of the U-partite
relevant core. -/
def ambientToRelevant
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (x : AmbientRelevantSet S α) :
    RelevantSet S α := by
  let αf := α.toFunctionEmbedding
  have hs : x.1 ∈ S.support αf := by
    rcases x.2 with ⟨e, a, hea⟩
    refine ⟨a, ?_⟩
    calc
      α a = S.part (e.1 a) := (e.2 a).symm
      _ = S.part x.1 := congrArg S.part hea
  refine ⟨⟨x.1, hs⟩, ?_⟩
  rcases x.2 with ⟨e, a, hea⟩
  exact ⟨e, a, hea⟩

@[simp] theorem ambientToRelevant_val
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (x : AmbientRelevantSet S α) :
    (ambientToRelevant S α x).1.1 = x.1 :=
  rfl

/-- The ambient relevant subsystem is closed-isomorphic to the relevant core
after relabelling its U-parts through alpha. -/
def ambientToCore
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D) :
    Partite.Closed.Embedding
      (ambientCore S α)
      ((core S α).relabel α.toFunctionEmbedding) := by
  let toFun : AmbientRelevantSet S α → RelevantSet S α :=
    ambientToRelevant S α
  let pe : Partite.Embedding
      (ambientCore S α)
      ((core S α).relabel α.toFunctionEmbedding) := {
    toFun := toFun
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : RelevantSet S α => z.1.1) hxy
    map_rel_iff := by
      intro R x
      change
        (S.restrict α.toFunctionEmbedding).rel R
          (Subtype.val ∘ (toFun ∘ x)) ↔
        S.rel R (Subtype.val ∘ x)
      change
        S.rel R
          (Subtype.val ∘ (Subtype.val ∘ (toFun ∘ x))) ↔
        S.rel R (Subtype.val ∘ x)
      constructor <;> intro h
      · convert h using 1
        funext i
        rfl
      · convert h using 1
        funext i
        rfl
    map_part := by
      intro x
      change
        α ((core S α).part (toFun x)) =
          S.part x.1
      exact S.restrictedPart_spec
        α.toFunctionEmbedding (toFun x).1
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  let z : AmbientRelevantSet S α :=
    ⟨y.1.1, by
      rcases y.2 with ⟨e, a, hea⟩
      exact ⟨e, a, hea⟩⟩
  refine ⟨z, ?_, ?_⟩
  · change
      S.rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x z)
    change
      (S.restrict α.toFunctionEmbedding).rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple (toFun ∘ x) y) at hy
    change
      S.rel (.inr F)
        (Subtype.val ∘
          (Subtype.val ∘ Structure.funcTuple (toFun ∘ x) y)) at hy
    have htuple :
        Subtype.val ∘ Structure.funcTuple x z =
          Subtype.val ∘
            (Subtype.val ∘ Structure.funcTuple (toFun ∘ x) y) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [z, toFun, Structure.funcTuple]
      · simp [toFun, Structure.funcTuple]
    exact Eq.mpr
      (congrArg
        (fun t => S.rel
          (show L.graph.Symbol from Sum.inr F) t) htuple)
      hy
  · apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The ambient relevant subsystem includes closedly into S for unary
functions. -/
def ambientCoreInclusionClosed_unary
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    (hUnary : ∀ F, L.funcArity F = 1) :
    Partite.Closed.Embedding (ambientCore S α) S := by
  let pe : Partite.Embedding (ambientCore S α) S :=
    Partite.System.inclusion S (AmbientRelevantSet S α)
  refine ⟨pe, ?_⟩
  exact (RelStructure.ClosedEmbedding.inclusion
    S.toRelStructure (AmbientRelevantSet S α)
    (ambientRelevant_functionClosed_unary S α hUnary)).closed

/-- Closed embeddings of the U-partite core relabel to the alpha-parts. -/
def relabelCoreEmbedding
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    {Y : Type v}
    {T : Partite.System L.graph U Y}
    (e : Partite.Closed.Embedding (core S α) T) :
    Partite.Closed.Embedding
      ((core S α).relabel α.toFunctionEmbedding)
      (T.relabel α.toFunctionEmbedding) :=
  relabelClosed e α.toFunctionEmbedding

/-- Convert a closed core embedding into the attaching map whose domain is the
ambient relevant subset of S. -/
def attachingMap
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    (S : Partite.System L.graph P X)
    (α : RelStructure.Embedding A D)
    {Y : Type v}
    {T : Partite.System L.graph U Y}
    (e : Partite.Closed.Embedding (core S α) T) :
    Partite.Closed.Embedding
      (S.induce (AmbientRelevantSet S α))
      (T.relabel α.toFunctionEmbedding) :=
  Partite.Closed.Embedding.comp
    (relabelCoreEmbedding S α e)
    (ambientToCore S α)

/-- Unary-function version of the missing local arbitrary-projection Picture
witness. -/
theorem localHalfClosedPicture_unary
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    [Finite U] [Finite P]
    {X : Type v} [Finite X]
    (S : Partite.System L.graph P X)
    (hSPartite : S.IsPartiteOver D)
    (hSU : S.FunctionOutputTransversal)
    (α : RelStructure.Embedding A D)
    (hUnary : ∀ F, L.funcArity F = 1)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (Y : Type v) (_ : Finite Y)
      (O : Partite.System L.graph P Y),
      O.IsPartiteOver D ∧
      O.FunctionOutputTransversal ∧
      Partite.HalfClosedArrow
        (A := Partite.Recursive.profile A D α)
        (B := S) (D := O) κ := by
  classical
  let C := core S α
  have hCPart : C.IsPartiteOver A :=
    core_isPartiteOver S hSPartite α
  have hCU : C.FunctionOutputTransversal :=
    core_uTransversal S hSU α
  obtain ⟨N, hN, hPowU, hArrow⟩ :=
    Partite.Closed.Induced.partiteLemma
      A C hCPart hCU κ
  let T := Partite.Induced.power C N
  have hTPart : T.IsPartiteOver A :=
    Partite.Induced.power_isPartiteOver hCPart hN
  let TP := T.relabel α.toFunctionEmbedding
  have hTPPart : TP.IsPartiteOver D :=
    Partite.Induced.relabel_isPartiteOver
      A T hTPart α
  have hTPU : TP.FunctionOutputTransversal :=
    uTransversal_relabel T α.toFunctionEmbedding hPowU
  let I := Partite.Closed.Embedding C T
  let maps : I →
      Partite.Closed.Embedding
        (S.induce (AmbientRelevantSet S α)) TP :=
    fun e => attachingMap S α e
  let O := Partite.Closed.Attachment.attach
    S (AmbientRelevantSet S α) TP maps
  have hOverlap :
      RelStructure.FunctionClosedSet S.toRelStructure
        (AmbientRelevantSet S α) :=
    ambientRelevant_functionClosed_unary S α hUnary
  have hOPart : O.IsPartiteOver D := by
    exact Partite.Attachment.attach_isPartiteOver
      S (AmbientRelevantSet S α) TP
      (fun e : I => (maps e).1)
      hSPartite hTPPart
  have hOU : O.FunctionOutputTransversal := by
    exact Partite.Closed.Attachment.uTransversal
      (B := S) (S := AmbientRelevantSet S α)
      (D := TP) (f := maps) hOverlap hSU hTPU
  refine ⟨_, inferInstance, O, hOPart, hOU, ?_⟩
  intro χ
  let coreEmb : Partite.Closed.Embedding TP O := by
    let pe : Partite.Embedding TP O :=
      Partite.Attachment.coreEmbedding
        S (AmbientRelevantSet S α) TP
        (fun e : I => (maps e).1)
    refine ⟨pe, ?_⟩
    exact Partite.Closed.Attachment.core_closed
      (B := S) (S := AmbientRelevantSet S α)
      (D := TP) (f := maps) hOverlap
  let colorCore : Partite.Closed.Embedding
      (Partite.transversal A) T → κ := fun e =>
    let ep : Partite.Closed.Embedding
        (Partite.Recursive.profile A D α) TP :=
      relabelClosed e α.toFunctionEmbedding
    χ (Partite.Closed.Embedding.comp coreEmb ep)
  obtain ⟨f, hf⟩ := hArrow colorCore
  let copyEmb : Partite.Closed.Embedding S O := by
    let pe : Partite.Embedding S O :=
      Partite.Attachment.copyEmbedding
        S (AmbientRelevantSet S α) TP
        (fun e : I => (maps e).1) f
    refine ⟨pe, ?_⟩
    exact Partite.Closed.Attachment.copy_closed
      (B := S) (S := AmbientRelevantSet S α)
      (D := TP) (f := maps) hOverlap f
  let lift :
      Partite.Closed.Embedding
          (Partite.Recursive.profile A D α) S →
        Partite.Closed.Embedding
          (Partite.Recursive.profile A D α) O :=
    fun e => Partite.Closed.Embedding.comp copyEmb e
  refine ⟨copyEmb.1, lift, ?_, ?_⟩
  · intro e x
    rfl
  · intro e₁ e₂
    let p₁ : Partite.Closed.ProjectedEmbedding A S α :=
      Partite.Recursive.profileEmbeddingToProjected e₁
    let p₂ : Partite.Closed.ProjectedEmbedding A S α :=
      Partite.Recursive.profileEmbeddingToProjected e₂
    let c₁ : Partite.Closed.Embedding (Partite.transversal A) C :=
      factorProjected S α p₁
    let c₂ : Partite.Closed.Embedding (Partite.transversal A) C :=
      factorProjected S α p₂
    have hm := hf c₁ c₂
    change colorCore (Partite.Closed.Embedding.comp f c₁) =
      colorCore (Partite.Closed.Embedding.comp f c₂) at hm
    have identify
        (e : Partite.Closed.Embedding
          (Partite.Recursive.profile A D α) S)
        (p : Partite.Closed.ProjectedEmbedding A S α)
        (hp : p =
          Partite.Recursive.profileEmbeddingToProjected e)
        (c : Partite.Closed.Embedding (Partite.transversal A) C)
        (hc : c = factorProjected S α p) :
        lift e =
          Partite.Closed.Embedding.comp coreEmb
            (relabelClosed
              (Partite.Closed.Embedding.comp f c)
              α.toFunctionEmbedding) := by
      subst p
      subst c
      apply Partite.Closed.Embedding.ext
      intro a
      let xa : AmbientRelevantSet S α :=
        ⟨e a, by
          exact ⟨
            Partite.Recursive.profileEmbeddingToProjected e,
            a, rfl⟩⟩
      have hext :=
        Partite.Attachment.copy_extends
          S (AmbientRelevantSet S α) TP
          (fun q : I => (maps q).1) f xa
      change
        copyEmb (e a) =
          coreEmb
            ((relabelClosed
              (Partite.Closed.Embedding.comp f
                (factorProjected S α
                  (Partite.Recursive.profileEmbeddingToProjected e)))
              α.toFunctionEmbedding) a)
      calc
        copyEmb (e a) =
            copyEmb xa.1 := rfl
        _ = coreEmb (maps f xa) := hext
        _ = coreEmb
            ((relabelClosed
              (Partite.Closed.Embedding.comp f
                (factorProjected S α
                  (Partite.Recursive.profileEmbeddingToProjected e)))
              α.toFunctionEmbedding) a) := by
              apply congrArg coreEmb
              apply Subtype.ext
              rfl
    have hi₁ := identify e₁ p₁ rfl c₁ rfl
    have hi₂ := identify e₂ p₂ rfl c₂ rfl
    rw [hi₁, hi₂]
    exact hm

/-- The exact local predicate required by the outer recursion holds for unary
function symbols. -/
theorem localPictures_unary
    {A : RelStructure L.graph U}
    {D : RelStructure L.graph P}
    [Finite U] [Finite P]
    (hUnary : ∀ F, L.funcArity F = 1)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    Partite.Recursive.LocalHalfClosedPictures A D κ := by
  intro X hX S hSPart hSU α
  letI : Finite X := hX
  exact localHalfClosedPicture_unary
    S hSPart hSU α hUnary κ

end StructuralRamsey.Partite.RelevantCorePicture
