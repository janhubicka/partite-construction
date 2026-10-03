import PartiteConstruction.Functional.SemiClosedAttachment
import PartiteConstruction.Functional.RecursiveConstruction

/-! # Semi-closed little picture for an arbitrary projection

This is the local construction missing from the simplified Appendix A proof.
The overlap is not all vertices in the selected parts.  It is the substructure
induced on vertices lying in relevant closed A-copies.  The closed partite
lemma is applied to that overlap.  All closed overlap embeddings into its
coordinate power are then extended to ordinary copies of the whole current
picture.

The resulting little picture need not be U-transversal, or even globally
semi-closed.  What is preserved is exactly what the second construction needs:
all relevant A-copies in the chosen extended copy remain closed.
-/
namespace StructuralRamsey.Partite.SemiClosed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

/-- A vertex belongs to the relevant overlap for alpha if it occurs in some
closed A-copy having projection alpha. -/
def Covered
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (x : V) : Prop :=
  ∃ e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a),
    ∃ a : U, e.1 a = x

def coveredSet
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D) : Set V :=
  {x | Covered A D B α x}

theorem covered_mem_support
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    {x : V}
    (hx : x ∈ coveredSet A D B α) :
    x ∈ B.support α.toFunctionEmbedding := by
  rcases hx with ⟨e, a, rfl⟩
  exact ⟨a, (e.2 a).symm⟩

/-- Relevant overlap seen with A-parts. -/
def restrictedSet
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D) :
    Set (B.support α.toFunctionEmbedding) :=
  {x | x.1 ∈ coveredSet A D B α}

noncomputable def restriction
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D) :
    Partite.System L.withFunctionDomains.graph U
      (restrictedSet A D B α) :=
  (B.restrict α.toFunctionEmbedding).induce
    (restrictedSet A D B α)

/-- Every relevant projected closed A-copy becomes a closed partite letter of
the relevant overlap. -/
noncomputable def restrictRelevant
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a)) :
    Partite.Closed.Embedding
      (Partite.transversal A)
      (restriction A D B α) := by
  let αf := α.toFunctionEmbedding
  let supportPoint (a : U) : B.support αf :=
    ⟨e.1 a, ⟨a, (e.2 a).symm⟩⟩
  let coveredPoint (a : U) :
      restrictedSet A D B α :=
    ⟨supportPoint a, ⟨e, a, rfl⟩⟩
  let pe : Partite.Embedding
      (Partite.transversal A)
      (restriction A D B α) := {
    toFun := coveredPoint
    injective := by
      intro a b hab
      apply e.1.toEmbedding.injective
      exact congrArg
        (fun q : restrictedSet A D B α => q.1.1) hab
    map_rel_iff := by
      intro R x
      change
        B.rel R
          ((fun q : restrictedSet A D B α => q.1.1) ∘
            (coveredPoint ∘ x)) ↔
          A.rel R x
      convert e.1.toEmbedding.map_rel_iff R x using 1
      funext i
      rfl
    map_part := by
      intro a
      change
        B.restrictedPart αf (supportPoint a) = a
      apply α.toEmbedding.injective
      exact
        (B.restrictedPart_spec αf (supportPoint a)).trans
          (e.2 a)
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hyB :
      B.rel (.inr F)
        (Structure.funcTuple
          (e.1 ∘ x) y.1.1) := by
    change
      B.rel (.inr F)
        ((fun q : restrictedSet A D B α => q.1.1) ∘
          Structure.funcTuple (pe ∘ x) y) at hy
    have ht :
        ((fun q : restrictedSet A D B α => q.1.1) ∘
            Structure.funcTuple (pe ∘ x) y) =
          Structure.funcTuple (e.1 ∘ x) y.1.1 := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [pe, coveredPoint, supportPoint,
          Structure.funcTuple, Function.comp_apply]
      · simp [pe, coveredPoint, supportPoint,
          Structure.funcTuple, Function.comp_apply]
    exact Eq.mp
      (congrArg (fun t => B.rel (.inr F) t) ht) hy
  obtain ⟨z, hz, hzy⟩ :=
    e.1.closed F x y.1.1 hyB
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hzy

/-- The relevant overlap remains A-partite. -/
theorem restriction_isPartiteOver
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.IsPartiteOver D) :
    (restriction A D B α).IsPartiteOver A := by
  let R0 := B.restrict α.toFunctionEmbedding
  have hR0 : R0.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver
      D B A hB α
  exact Partite.System.induce_isPartiteOver hR0

theorem restriction_singleValued
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.FunctionOutputSingleValued) :
    (restriction A D B α).FunctionOutputSingleValued := by
  exact Partite.System.induce_singleValued
    (Partite.System.restrict_singleValued
      α.toFunctionEmbedding hB)

theorem restriction_outputImpliesDomain
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.OutputImpliesDomain) :
    (restriction A D B α).OutputImpliesDomain := by
  exact Partite.System.induce_outputImpliesDomain
    (Partite.System.restrict_outputImpliesDomain
      α.toFunctionEmbedding hB)

/-- Same relations as the relevant overlap but with the original outer parts. -/
noncomputable def overlapToRestriction
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D) :
    Partite.Closed.Embedding
      (B.induce (coveredSet A D B α))
      ((restriction A D B α).relabel
        α.toFunctionEmbedding) := by
  let αf := α.toFunctionEmbedding
  let toInner
      (x : coveredSet A D B α) :
      restrictedSet A D B α :=
    ⟨⟨x.1, covered_mem_support A D B α x.2⟩, x.2⟩
  let pe : Partite.Embedding
      (B.induce (coveredSet A D B α))
      ((restriction A D B α).relabel αf) := {
    toFun := toInner
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg
        (fun q : restrictedSet A D B α => q.1.1) h
    map_rel_iff := by
      intro R x
      change
        B.rel R
          ((fun q : restrictedSet A D B α => q.1.1) ∘
            (toInner ∘ x)) ↔
          B.rel R (Subtype.val ∘ x)
      congr 1
      funext i
      rfl
    map_part := by
      intro x
      change
        α (B.restrictedPart αf
          ⟨x.1, covered_mem_support A D B α x.2⟩) =
          B.part x.1
      exact B.restrictedPart_spec αf _
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  refine ⟨y, ?_, ?_⟩
  · change
      B.rel (.inr F)
        (Subtype.val ∘ Structure.funcTuple x y)
    change
      B.rel (.inr F)
        ((fun q : restrictedSet A D B α => q.1.1) ∘
          Structure.funcTuple (pe ∘ x) (pe y)) at hy
    convert hy using 1
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> rfl
  · rfl

/-- Closed embeddings of the inner overlap may be relabelled to outer parts. -/
def Partite.Closed.Embedding.relabel
    {Q : Type v}
    {C : Partite.System L.withFunctionDomains.graph U V}
    {E : Partite.System L.withFunctionDomains.graph U W}
    (f : Partite.Closed.Embedding C E)
    (α : U ↪ Q) :
    Partite.Closed.Embedding
      (C.relabel α) (E.relabel α) :=
  ⟨f.1.relabel α, f.2⟩

/-- Convert one closed overlap embedding into the outer-part attaching map. -/
noncomputable def attachingMap
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    {E : Partite.System L.withFunctionDomains.graph U W}
    (f : Partite.Closed.Embedding
      (restriction A D B α) E) :
    Partite.Closed.Embedding
      (B.induce (coveredSet A D B α))
      (E.relabel α.toFunctionEmbedding) :=
  Partite.Closed.Embedding.comp
    (f.relabel α.toFunctionEmbedding)
    (overlapToRestriction A D B α)

/-- Vertex type of the arbitrary-projection little picture. -/
abbrev Vertex
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W) :=
  Partite.Attachment.Vertex
    (coveredSet A D B α) W
    (Partite.Closed.Embedding
      (restriction A D B α) E)

/-- Extend every closed copy of the relevant overlap to an ordinary copy of B. -/
noncomputable def build
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W) :
    Partite.System L.withFunctionDomains.graph P
      (Vertex A D B α E) :=
  Partite.Attachment.attach
    B (coveredSet A D B α)
    (E.relabel α.toFunctionEmbedding)
    (fun f => (attachingMap A D B α f).1)


/-- Extend one closed overlap embedding to the ordinary B-copy and retain
closedness on a relevant A-subcopy. -/
noncomputable def selectedLift
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (f : Partite.Closed.Embedding
      (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a)) :
    Partite.Closed.Embedding
      (Partite.Recursive.profile A D α)
      (build A D B α E) := by
  let maps :=
    fun g : Partite.Closed.Embedding
        (restriction A D B α) E =>
      attachingMap A D B α g
  let copy :
      Partite.Embedding B (build A D B α E) :=
    Partite.Attachment.copyEmbedding
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g => (maps g).1) f
  let pe : Partite.Embedding
      (Partite.Recursive.profile A D α)
      (build A D B α E) := {
    toEmbedding :=
      copy.toEmbedding.comp e.1.toEmbedding
    map_part := by
      intro a
      exact (copy.map_part (e.1 a)).trans (e.2 a)
  }
  refine ⟨pe, ?_⟩
  have heCovered :
      ∀ a : U, e.1 a ∈ coveredSet A D B α :=
    fun a => ⟨e, a, rfl⟩
  exact Partite.Attachment.selectedCopy_closed
    (A := A) (B := B)
    (S := coveredSet A D B α)
    (D := E.relabel α.toFunctionEmbedding)
    (f := maps)
    hAtotal hBroot hBsingle f e.1 heCovered

@[simp] theorem selectedLift_apply
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (f : Partite.Closed.Embedding
      (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a))
    (a : U) :
    selectedLift A D B α E hAtotal hBroot hBsingle f e a =
      Partite.Attachment.copyEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        f (e.1 a) :=
  rfl


/-- On a relevant A-copy, the selected attached copy agrees with the core map
coming from the overlap embedding. -/
theorem selectedLift_core
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (f : Partite.Closed.Embedding
      (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a))
    (a : U) :
    selectedLift A D B α E hAtotal hBroot hBsingle f e a =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (f (restrictRelevant A D B α e a)) := by
  let x : coveredSet A D B α :=
    ⟨e.1 a, ⟨e, a, rfl⟩⟩
  have hcopy :=
    Partite.Attachment.copy_extends
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g : Partite.Closed.Embedding
        (restriction A D B α) E =>
          (attachingMap A D B α g).1)
      f x
  rw [selectedLift_apply]
  calc
    Partite.Attachment.copyEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        f (e.1 a) =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        ((attachingMap A D B α f) x) := hcopy
    _ =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (f (restrictRelevant A D B α e a)) := by
      congr 1
      change
        f (overlapToRestriction A D B α x) =
          f (restrictRelevant A D B α e a)
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rfl

/-- A core A-letter is relevant if it factors through one closed overlap copy
and one A-copy coming from the previous picture. -/
def CoreLiftable
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E) : Prop :=
  ∃ f : Partite.Closed.Embedding
      (restriction A D B α) E,
    ∃ e : Partite.Closed.ProjectedEmbedding
      A B (fun a => α a),
      d = Partite.Closed.Embedding.comp
        f (restrictRelevant A D B α e)

/-- Turn a liftable core letter into the corresponding closed projected copy
in the little picture. -/
noncomputable def liftCore
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (hd : CoreLiftable A D B α E d) :
    Partite.Closed.Embedding
      (Partite.Recursive.profile A D α)
      (build A D B α E) := by
  let f := Classical.choose hd
  let he := Classical.choose_spec hd
  let e := Classical.choose he
  exact
    selectedLift A D B α E
      hAtotal hBroot hBsingle f e

theorem liftCore_apply
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (hd : CoreLiftable A D B α E d)
    (a : U) :
    liftCore A D B α E hAtotal hBroot hBsingle d hd a =
      Partite.Attachment.coreEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding
          (restriction A D B α) E =>
            (attachingMap A D B α g).1)
        (d a) := by
  let f := Classical.choose hd
  have he := Classical.choose_spec hd
  let e := Classical.choose he
  have hfac : d =
      Partite.Closed.Embedding.comp
        f (restrictRelevant A D B α e) :=
    Classical.choose_spec he
  change
    selectedLift A D B α E
      hAtotal hBroot hBsingle f e a = _
  rw [selectedLift_core]
  congr 1
  have happ := congrArg
    (fun q : Partite.Closed.Embedding
      (Partite.transversal A) E => q a) hfac
  exact happ.symm

theorem liftCore_unique
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (d : Partite.Closed.Embedding
      (Partite.transversal A) E)
    (h₁ h₂ : CoreLiftable A D B α E d) :
    liftCore A D B α E hAtotal hBroot hBsingle d h₁ =
      liftCore A D B α E hAtotal hBroot hBsingle d h₂ := by
  apply Partite.Closed.Embedding.ext
  intro a
  rw [liftCore_apply, liftCore_apply]

end StructuralRamsey.Partite.SemiClosed.Picture
