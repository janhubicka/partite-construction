import PartiteConstruction.Functional.SemiClosedAttachment
import PartiteConstruction.Functional.RecursiveConstruction

/-! # Semi-closed little picture for an arbitrary projection

This is the local construction missing from the simplified Appendix A proof.
The overlap is the induced subsystem on vertices lying in relevant closed
A-copies with the prescribed projection. The closed partite lemma is applied
to this overlap and every closed overlap embedding is then extended to an
ordinary copy of the whole current picture.

The resulting little picture need not be U-transversal or globally
singleton-valued. The only closure assertion needed for the sandwich is that
the relevant A-subcopies of the selected extended copy remain closed.
-/
namespace StructuralRamsey.Partite.SemiClosed.Picture

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W : Type v}

def Covered
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (x : V) : Prop :=
  ∃ e : Partite.Closed.ProjectedEmbedding A B (fun a => α a),
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
    {x : V} (hx : x ∈ coveredSet A D B α) :
    x ∈ B.support α.toFunctionEmbedding := by
  rcases hx with ⟨e, a, rfl⟩
  exact ⟨a, (e.2 a).symm⟩

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

noncomputable def restrictRelevant
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (e : Partite.Closed.ProjectedEmbedding A B (fun a => α a)) :
    Partite.Closed.Embedding
      (Partite.transversal A) (restriction A D B α) := by
  let αf := α.toFunctionEmbedding
  let supportPoint (a : U) : B.support αf :=
    ⟨e.1 a, ⟨a, (e.2 a).symm⟩⟩
  let coveredPoint (a : U) : restrictedSet A D B α :=
    ⟨supportPoint a, ⟨e, a, rfl⟩⟩
  let pe : Partite.Embedding
      (Partite.transversal A) (restriction A D B α) := {
    toFun := coveredPoint
    injective := by
      intro a b hab
      apply e.1.toEmbedding.injective
      exact congrArg (fun q : restrictedSet A D B α => q.1.1) hab
    map_rel_iff := by
      intro R x
      change
        B.rel R
          ((fun q : restrictedSet A D B α => q.1.1) ∘
            (coveredPoint ∘ x)) ↔ A.rel R x
      have hfun :
          ((fun q : restrictedSet A D B α => q.1.1) ∘
              (coveredPoint ∘ x)) = e.1.toEmbedding ∘ x := by
        funext i
        rfl
      rw [hfun]
      exact e.1.toEmbedding.map_rel_iff R x
    map_part := by
      intro a
      change B.restrictedPart αf (supportPoint a) = a
      exact α.injective
        ((B.restrictedPart_spec αf (supportPoint a)).trans (e.2 a))
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hyB :
      B.rel (.inr F) (Structure.funcTuple (e.1 ∘ x) y.1.1) := by
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
    exact Eq.mp (congrArg (fun t => B.rel (.inr F) t) ht) hy
  obtain ⟨z, hz, hzy⟩ := e.1.closed F x y.1.1 hyB
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hzy

theorem restriction_isPartiteOver
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.IsPartiteOver D) :
    (restriction A D B α).IsPartiteOver A := by
  let R0 := B.restrict α.toFunctionEmbedding
  have hR0 : R0.IsPartiteOver A :=
    Partite.Induced.restrict_isPartiteOver D B A hB α
  exact Partite.System.induce_isPartiteOver hR0

theorem restriction_singleValued
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.FunctionOutputSingleValued) :
    (restriction A D B α).FunctionOutputSingleValued := by
  exact Partite.System.induce_singleValued
    (Partite.System.restrict_singleValued α.toFunctionEmbedding hB)

theorem restriction_outputImpliesDomain
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (hB : B.OutputImpliesDomain) :
    (restriction A D B α).OutputImpliesDomain := by
  exact Partite.System.induce_outputImpliesDomain
    (Partite.System.restrict_outputImpliesDomain α.toFunctionEmbedding hB)

noncomputable def overlapToRestriction
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D) :
    Partite.Closed.Embedding
      (B.induce (coveredSet A D B α))
      ((restriction A D B α).relabel α.toFunctionEmbedding) := by
  let αf := α.toFunctionEmbedding
  let toInner (x : coveredSet A D B α) :
      restrictedSet A D B α :=
    ⟨⟨x.1, covered_mem_support A D B α x.2⟩, x.2⟩
  let pe : Partite.Embedding
      (B.induce (coveredSet A D B α))
      ((restriction A D B α).relabel αf) := {
    toFun := toInner
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun q : restrictedSet A D B α => q.1.1) h
    map_rel_iff := by
      intro R x
      change
        B.rel R
          ((fun q : restrictedSet A D B α => q.1.1) ∘
            (toInner ∘ x)) ↔ B.rel R (Subtype.val ∘ x)
      have hfun :
          ((fun q : restrictedSet A D B α => q.1.1) ∘
              (toInner ∘ x)) = Subtype.val ∘ x := by
        funext i
        rfl
      rw [hfun]
    map_part := by
      intro x
      change
        α (B.restrictedPart αf
          ⟨x.1, covered_mem_support A D B α x.2⟩) = B.part x.1
      exact B.restrictedPart_spec αf _
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  let z : coveredSet A D B α := ⟨y.1.1, y.2⟩
  refine ⟨z, ?_, ?_⟩
  · change B.rel (.inr F)
      (Subtype.val ∘ Structure.funcTuple x z)
    change
      B.rel (.inr F)
        ((fun q : restrictedSet A D B α => q.1.1) ∘
          Structure.funcTuple (pe ∘ x) y) at hy
    have ht :
        ((fun q : restrictedSet A D B α => q.1.1) ∘
            Structure.funcTuple (pe ∘ x) y) =
          Subtype.val ∘ Structure.funcTuple x z := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [pe, toInner, z, Structure.funcTuple, Function.comp_apply]
      · simp [pe, toInner, z, Structure.funcTuple, Function.comp_apply]
    exact Eq.mp (congrArg (fun t => B.rel (.inr F) t) ht) hy
  · apply Subtype.ext
    apply Subtype.ext
    rfl

def relabelClosed
    {Q : Type v}
    {C : Partite.System L.withFunctionDomains.graph U V}
    {E : Partite.System L.withFunctionDomains.graph U W}
    (f : Partite.Closed.Embedding C E) (α : U ↪ Q) :
    Partite.Closed.Embedding (C.relabel α) (E.relabel α) :=
  ⟨f.1.relabel α, f.2⟩

noncomputable def attachingMap
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    {E : Partite.System L.withFunctionDomains.graph U W}
    (f : Partite.Closed.Embedding (restriction A D B α) E) :
    Partite.Closed.Embedding
      (B.induce (coveredSet A D B α))
      (E.relabel α.toFunctionEmbedding) :=
  Partite.Closed.Embedding.comp
    (relabelClosed f α.toFunctionEmbedding)
    (overlapToRestriction A D B α)

abbrev Vertex
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W) :=
  Partite.Attachment.Vertex
    (coveredSet A D B α)
    (W := W)
    (I := Partite.Closed.Embedding (restriction A D B α) E)

noncomputable def build
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W) :
    Partite.System L.withFunctionDomains.graph P (Vertex A D B α E) :=
  Partite.Attachment.attach
    B (coveredSet A D B α)
    (E.relabel α.toFunctionEmbedding)
    (fun f => (attachingMap A D B α f).1)

noncomputable def selectedLift
    (A : RelStructure L.withFunctionDomains.graph U)
    (D : RelStructure L.withFunctionDomains.graph P)
    (B : Partite.System L.withFunctionDomains.graph P V)
    (α : RelStructure.Embedding A D)
    (E : Partite.System L.withFunctionDomains.graph U W)
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (f : Partite.Closed.Embedding (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding A B (fun a => α a)) :
    Partite.Closed.Embedding
      (Partite.Recursive.profile A D α) (build A D B α E) := by
  let maps :=
    fun g : Partite.Closed.Embedding (restriction A D B α) E =>
      attachingMap A D B α g
  let copy : Partite.Embedding B (build A D B α E) :=
    Partite.Attachment.copyEmbedding
      B (coveredSet A D B α)
      (E.relabel α.toFunctionEmbedding)
      (fun g => (maps g).1) f
  let pe : Partite.Embedding
      (Partite.Recursive.profile A D α) (build A D B α E) := {
    toEmbedding := copy.toEmbedding.comp e.1.toEmbedding
    map_part := by
      intro a
      exact (copy.map_part (e.1 a)).trans (e.2 a)
  }
  refine ⟨pe, ?_⟩
  have heCovered : ∀ a : U, e.1 a ∈ coveredSet A D B α :=
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
    (f : Partite.Closed.Embedding (restriction A D B α) E)
    (e : Partite.Closed.ProjectedEmbedding A B (fun a => α a))
    (a : U) :
    selectedLift A D B α E hAtotal hBroot hBsingle f e a =
      Partite.Attachment.copyEmbedding
        B (coveredSet A D B α)
        (E.relabel α.toFunctionEmbedding)
        (fun g : Partite.Closed.Embedding (restriction A D B α) E =>
          (attachingMap A D B α g).1)
        f (e.1 a) :=
  rfl

end StructuralRamsey.Partite.SemiClosed.Picture
