import PartiteConstruction.Functional.IsolatedCommonLabelGlue

/-! # Finite diaries of isolated functional A-boundaries

In the recursive analysis of a closed attachment test, previously exposed
overlaps all lie in the core/rest side.  We record each such overlap as a
closed partial A-boundary together with an isolated target A-copy.  These
certificates survive target embeddings and, crucially, survive gluing a new
piece onto the left while the recorded boundary stays on the right.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U W Y Z : Type v}
variable {A : Structure L U} {C : Structure L W}

/-- A closed partial copy of A embedded in a source structure.  The labels are
the literal A-elements of the closed support. -/
structure BoundaryRequest (A : Structure L U) (C : Structure L W) where
  support : Set U
  supportClosed : A.IsClosed support
  embedding : Embedding (A.induce support supportClosed) C

namespace BoundaryRequest

/-- Re-present an arbitrary embedded partial A-copy by the literal closed
range of its label embedding.  This makes boundary requests homogeneous enough
to store in one finite diary even when the original overlap carriers differ. -/
noncomputable def embeddedFromRange
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) :
    Embedding
      (A.induce (Set.range ell) ell.range_isClosed) R := by
  classical
  let inc : Embedding
      (A.induce (Set.range ell) ell.range_isClosed) A :=
    inclusion A (Set.range ell) ell.range_isClosed
  have hrange :
      ∀ z : Set.range ell, ∃ x : X, inc z = ell x := by
    intro z
    rcases z.2 with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  exact inc.factorThroughClosedRange ell hrange

theorem embeddedFromRange_spec
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A)
    (z : Set.range ell) :
    ell (embeddedFromRange ell z) = z.1 := by
  classical
  let inc : Embedding
      (A.induce (Set.range ell) ell.range_isClosed) A :=
    inclusion A (Set.range ell) ell.range_isClosed
  have hrange :
      ∀ w : Set.range ell, ∃ x : X, inc w = ell x := by
    intro w
    rcases w.2 with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  have h :=
    Embedding.factorThroughClosedRange_spec inc ell hrange z
  exact h

/-- Normalize an arbitrary embedded labelled boundary to a literal closed
support of A. -/
noncomputable def ofEmbeddedLabels
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) (e : Embedding R C) :
    BoundaryRequest A C where
  support := Set.range ell
  supportClosed := ell.range_isClosed
  embedding := e.comp (embeddedFromRange ell)

/-- A relative witness for an arbitrary embedded labelled boundary yields an
isolated diary entry after range normalization. -/
theorem isolated_ofEmbeddedLabels
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) (e : Embedding R C)
    {TCarrier : Type v} {T : Structure L TCarrier}
    (f : W → TCarrier) (targetCopy : Embedding A T)
    (hcompat : ∀ x : X, f (e x) = targetCopy (ell x))
    (hiso : ∀ y : W, ∀ a : U, f y = targetCopy a →
      ∃ x : X, y = e x ∧ ell x = a) :
    IsolatedBoundary (ofEmbeddedLabels ell e) T f := by
  classical
  refine ⟨targetCopy, ?_, ?_⟩
  · intro z
    change
      f (e (embeddedFromRange ell z)) = targetCopy z.1
    calc
      f (e (embeddedFromRange ell z)) =
          targetCopy (ell (embeddedFromRange ell z)) :=
        hcompat (embeddedFromRange ell z)
      _ = targetCopy z.1 :=
        congrArg targetCopy (embeddedFromRange_spec ell z)
  · intro y a hya
    obtain ⟨x, hyx, hxa⟩ := hiso y a hya
    let z : Set.range ell := ⟨ell x, ⟨x, rfl⟩⟩
    refine ⟨z, ?_, ?_⟩
    · change y = e (embeddedFromRange ell z)
      calc
        y = e x := hyx
        _ = e (embeddedFromRange ell z) := by
          apply congrArg e
          apply ell.injective
          calc
            ell x = z.1 := rfl
            _ = ell (embeddedFromRange ell z) :=
              (embeddedFromRange_spec ell z).symm
    · change z.1 = a
      exact hxa

/-- Transport a boundary forward along a full source embedding. -/
def postcomp
    {X : Type v} {C' : Structure L X}
    (r : BoundaryRequest A C) (j : Embedding C C') :
    BoundaryRequest A C' where
  support := r.support
  supportClosed := r.supportClosed
  embedding := j.comp r.embedding

end BoundaryRequest

/-- A boundary request together with the full A-copy in the projection target
through which its literal A-labels project.  These are precisely the diary
entries produced by closed partite overlaps. -/
structure ProjectedBoundaryRequest
    {P : Type v} (A : Structure L U) (D : Structure L P)
    (C : Structure L W) (p : W → P) where
  boundary : BoundaryRequest A C
  beta : Embedding A D
  projection :
    ∀ x, p (boundary.embedding x) = beta x.1

namespace ProjectedBoundaryRequest

/-- Normalize an arbitrary embedded labelled boundary and remember its
projection through a full A-copy of D. -/
noncomputable def ofEmbeddedLabels
    {P X : Type v} {D : Structure L P} {R : Structure L X}
    {p : W → P}
    (ell : Embedding R A) (beta : Embedding A D)
    (e : Embedding R C)
    (hproj : ∀ x, p (e x) = beta (ell x)) :
    ProjectedBoundaryRequest A D C p where
  boundary := BoundaryRequest.ofEmbeddedLabels ell e
  beta := beta
  projection := by
    intro z
    change
      p (e (BoundaryRequest.embeddedFromRange ell z)) = beta z.1
    calc
      p (e (BoundaryRequest.embeddedFromRange ell z)) =
          beta (ell (BoundaryRequest.embeddedFromRange ell z)) :=
        hproj (BoundaryRequest.embeddedFromRange ell z)
      _ = beta z.1 :=
        congrArg beta (BoundaryRequest.embeddedFromRange_spec ell z)

/-- Transport a projected boundary through a full source embedding whose
outer projection commutes with the old one. -/
def postcomp
    {P X : Type v} {D : Structure L P} {C' : Structure L X}
    {p : W → P} {p' : X → P}
    (r : ProjectedBoundaryRequest A D C p)
    (j : Embedding C C')
    (hcomm : ∀ x, p' (j x) = p x) :
    ProjectedBoundaryRequest A D C' p' where
  boundary := r.boundary.postcomp j
  beta := r.beta
  projection := by
    intro x
    calc
      p' ((r.boundary.postcomp j).embedding x) =
          p (r.boundary.embedding x) := hcomm _
      _ = r.beta x.1 := r.projection x

end ProjectedBoundaryRequest

/-- A witness map realizes a boundary inside one target A-copy and no source
point outside the boundary leaks into that copy. -/
def IsolatedBoundary
    (r : BoundaryRequest A C)
    (T : Structure L Y) (f : W → Y) : Prop :=
  ∃ targetCopy : Embedding A T,
    (∀ x, f (r.embedding x) = targetCopy x.1) ∧
    ∀ y a, f y = targetCopy a →
      ∃ x, y = r.embedding x ∧ x.1 = a

namespace IsolatedBoundary

/-- An isolated boundary is exactly a root-isolation certificate with the
canonical inclusion of its closed support into A. -/
theorem toRootIsolated
    {r : BoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (h : IsolatedBoundary r T f) :
    ∃ targetCopy : Embedding A T,
      (∀ x, f (r.embedding x) = targetCopy x.1) ∧
      IsFreeAmalgam.RootIsolated
        r.embedding targetCopy
        (inclusion A r.support r.supportClosed) f := by
  obtain ⟨targetCopy, hcompat, hiso⟩ := h
  refine ⟨targetCopy, hcompat, ?_⟩
  intro y a hya
  obtain ⟨x, hyx, hxa⟩ := hiso y a hya
  refine ⟨x, hyx, ?_⟩
  exact hxa

/-- Isolation of a range-normalized diary entry recovers the original
embedded labelled boundary, with its original carrier and label embedding. -/
theorem toEmbeddedLabels
    {X : Type v} {R : Structure L X}
    (ell : Embedding R A) (e : Embedding R C)
    {T : Structure L Y} {f : W → Y}
    (h :
      IsolatedBoundary
        (BoundaryRequest.ofEmbeddedLabels ell e) T f) :
    ∃ targetCopy : Embedding A T,
      (∀ x : X, f (e x) = targetCopy (ell x)) ∧
      IsFreeAmalgam.RootIsolated e targetCopy ell f := by
  classical
  obtain ⟨targetCopy, hcompat0, hiso0⟩ := h
  have hfrom (x : X) :
      BoundaryRequest.embeddedFromRange ell
        (⟨ell x, ⟨x, rfl⟩⟩ : Set.range ell) = x := by
    apply ell.injective
    calc
      ell
          (BoundaryRequest.embeddedFromRange ell
            (⟨ell x, ⟨x, rfl⟩⟩ : Set.range ell)) =
          ell x :=
        BoundaryRequest.embeddedFromRange_spec ell
          (⟨ell x, ⟨x, rfl⟩⟩ : Set.range ell)
  have hcompat :
      ∀ x : X, f (e x) = targetCopy (ell x) := by
    intro x
    let z : Set.range ell := ⟨ell x, ⟨x, rfl⟩⟩
    have hz := hcompat0 z
    change
      f (e (BoundaryRequest.embeddedFromRange ell z)) =
        targetCopy z.1 at hz
    simpa [z, hfrom x] using hz
  refine ⟨targetCopy, hcompat, ?_⟩
  intro y a hya
  obtain ⟨z, hyz, hza⟩ := hiso0 y a hya
  let x : X := BoundaryRequest.embeddedFromRange ell z
  refine ⟨x, ?_, ?_⟩
  · exact hyz
  · calc
      ell x = z.1 :=
        BoundaryRequest.embeddedFromRange_spec ell z
      _ = a := hza

/-- Isolation survives postcomposition of the target by a full embedding. -/
theorem postcompTarget
    {r : BoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (h : IsolatedBoundary r T f)
    {T' : Structure L Z} (j : Embedding T T') :
    IsolatedBoundary r T' (j ∘ f) := by
  obtain ⟨targetCopy, hcompat, hiso⟩ := h
  let targetCopy' : Embedding A T' := j.comp targetCopy
  refine ⟨targetCopy', ?_, ?_⟩
  · intro x
    exact congrArg j (hcompat x)
  · intro y a hya
    have hya0 : f y = targetCopy a := by
      apply j.injective
      exact hya
    obtain ⟨x, hyx, hxa⟩ := hiso y a hya0
    exact ⟨x, hyx, hxa⟩

end IsolatedBoundary

/-- A tree witness carrying isolated copies for every request in a finite
boundary diary. -/
def BoundaryDiaryWitness
    {VB : Type v} (Base : Structure L VB)
    (requests : List (BoundaryRequest A C)) : Prop :=
  ∃ (TCarrier : Type v) (T : Structure L TCarrier),
    TreeAmalgam Base TCarrier T ∧
    ∃ f : W → TCarrier,
      C.IsHomomorphismEmbedding T f ∧
      ∀ r ∈ requests, IsolatedBoundary r T f

namespace IsFreeAmalgam

variable {H E F Whole G TE TF T : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {WholeS : Structure L Whole}
variable {Gov : Structure L G}
variable {TL : Structure L TE} {TR : Structure L TF}
variable {Target : Structure L T}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left WholeS} {iR : Embedding Right WholeS}
variable {tL : Embedding Gov TL} {tR : Embedding Gov TR}
variable {jL : Embedding TL Target} {jR : Embedding TR Target}

/-- An isolated boundary on the right side remains isolated after a compatible
functional lift. -/
theorem lift_preservesRightBoundary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G)
    (fL : E → TE) (fR : F → TF)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (r : BoundaryRequest A Right)
    (hr : IsolatedBoundary r TR fR) :
    let f :=
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
    IsolatedBoundary (r.postcomp iR) Target f := by
  classical
  obtain ⟨targetCopy, hsec, hsecIso⟩ := hr.toRootIsolated
  have hpersist :=
    functionalLiftMap_preservesRightRoot
      hSrc hTgt q fL fR hcompatL hcompatR hrootL
      r.embedding targetCopy
      (inclusion A r.support r.supportClosed)
      (fun x => by
        change fR (r.embedding x) = targetCopy x.1
        exact hsec x)
      hsecIso
  let f :=
    functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
  refine ⟨jR.comp targetCopy, ?_, ?_⟩
  · intro x
    exact hpersist.1 x
  · intro y a hya
    obtain ⟨x, hyx, hxa⟩ := hpersist.2 y a hya
    refine ⟨x, hyx, ?_⟩
    exact hxa


/-- A finite diary of isolated right-side boundaries survives the same
compatible functional lift.  This is the list-level persistence interface
used by the recursive closed-attachment proof. -/
theorem lift_preservesRightDiary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G)
    (fL : E → TE) (fR : F → TF)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (requests : List (BoundaryRequest A Right))
    (hDiary :
      ∀ r ∈ requests, IsolatedBoundary r TR fR) :
    let f :=
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
    ∀ r ∈ requests,
      IsolatedBoundary (r.postcomp iR) Target f := by
  intro f r hr
  exact lift_preservesRightBoundary
    hSrc hTgt q fL fR hcompatL hcompatR hrootL
    r (hDiary r hr)


/-- Glue isolated common A-labels while carrying both an arbitrary source
history and a finite diary of older boundaries living on the right side.

This is the recursive closed-attachment primitive: the newly exposed overlap
is used as the gluing root, while all previously exposed overlaps remain in
the rest/core side and are transported through the compatible lift. -/
theorem glueIsolatedCommonLabels_withHistoryAndRightDiary
    {VB : Type v} {Base : Structure L VB}
    (hA : A.Irreducible)
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTreeL : TreeAmalgam Base TE TL)
    (hTreeR : TreeAmalgam Base TF TR)
    (targetL : Embedding A TL)
    (targetR : Embedding A TR)
    (q : H → U) (hq : Function.Injective q)
    (fL : E → TE) (fR : F → TF)
    (hcompatL : ∀ d, fL (sL d) = targetL (q d))
    (hcompatR : ∀ d, fR (sR d) = targetR (q d))
    (hfL : Left.IsHomomorphismEmbedding TL fL)
    (hfR : Right.IsHomomorphismEmbedding TR fR)
    (hrootL : RootIsolated sL targetL q fL)
    (hrootR : RootIsolated sR targetR q fR)
    (history : List (Set Whole))
    (hHistL :
      ∀ Hset ∈ history, ∀ x y : E,
        fL x = fL y → (iL x ∈ Hset ↔ iL y ∈ Hset))
    (hHistR :
      ∀ Hset ∈ history, ∀ x y : F,
        fR x = fR y → (iR x ∈ Hset ↔ iR y ∈ Hset))
    (requests : List (BoundaryRequest A Right))
    (hDiaryR :
      ∀ r ∈ requests, IsolatedBoundary r TR fR) :
    ∃ (Z0 : Type v) (Target0 : Structure L Z0),
      TreeAmalgam Base Z0 Target0 ∧
      ∃ f : Whole → Z0,
        WholeS.IsHomomorphismEmbedding Target0 f ∧
        (∀ Hset ∈ history, ∀ x y : Whole,
          f x = f y → (x ∈ Hset ↔ y ∈ Hset)) ∧
        ∀ r ∈ requests,
          IsolatedBoundary (r.postcomp iR) Target0 f := by
  classical
  let Target0 :=
    FreeAmalgam.amalgam A TL TR targetL targetR
  let jL :=
    FreeAmalgam.leftEmbedding A TL TR targetL targetR
  let jR :=
    FreeAmalgam.rightEmbedding A TL TR targetL targetR
  have hcL : targetL.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetL, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hcR : targetR.ContainedInIrreducible := by
    refine ⟨U, A, hA, targetR, ?_⟩
    intro a
    exact ⟨a, rfl⟩
  have hTree :
      TreeAmalgam Base
        (FreeAmalgam.Vertex A TL TR targetL targetR) Target0 :=
    FreeAmalgam.treeAmalgam A TL TR targetL targetR Base
      hTreeL hTreeR hcL hcR
  have hTgt :
      IsFreeAmalgam targetL targetR jL jR :=
    FreeAmalgam.isFreeAmalgam A TL TR targetL targetR
  let f : Whole → FreeAmalgam.Vertex A TL TR targetL targetR :=
    functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
  have hf : WholeS.IsHomomorphismEmbedding Target0 f :=
    functionalLiftMap_isHomomorphismEmbedding
      hSrc hTgt q fL fR hcompatL hcompatR
      hfL hfR hrootL hrootR
  have hHist :
      ∀ Hset ∈ history, ∀ x y : Whole,
        f x = f y → (x ∈ Hset ↔ y ∈ Hset) :=
    functionalLiftMap_respectsSourceSets
      hSrc hTgt q hq fL fR hcompatL hcompatR
      hrootL hrootR history hHistL hHistR
  have hDiary :
      ∀ r ∈ requests,
        IsolatedBoundary (r.postcomp iR) Target0 f :=
    lift_preservesRightDiary
      hSrc hTgt q fL fR hcompatL hcompatR hrootL
      requests hDiaryR
  exact ⟨_, Target0, hTree, f, hf, hHist, hDiary⟩

end IsFreeAmalgam

end StructuralRamsey.Structure
