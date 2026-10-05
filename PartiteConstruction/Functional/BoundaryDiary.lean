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

/-- Transport a boundary forward along a full source embedding. -/
def postcomp
    {X : Type v} {C' : Structure L X}
    (r : BoundaryRequest A C) (j : Embedding C C') :
    BoundaryRequest A C' where
  support := r.support
  supportClosed := r.supportClosed
  embedding := j.comp r.embedding

end BoundaryRequest

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

end IsFreeAmalgam

end StructuralRamsey.Structure
