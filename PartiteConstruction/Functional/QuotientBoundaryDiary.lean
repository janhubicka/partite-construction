import PartiteConstruction.Functional.BoundaryDiary

/-! # Quotient-labelled functional boundary diaries

The closed-attachment diary uses boundaries whose labels embed into the
control structure A.  Reducible separators in the Hales--Jewett core need a
slightly more general interface: several separator vertices may have the same
A-label.  The functional free-amalgam glue already supports such a label map;
only the diary datatype had unnecessarily required injective labels.

This file records heterogeneous source boundaries together with arbitrary
label maps into A and the corresponding root-isolation certificates.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U W Y Z : Type v}
variable {A : Structure L U} {C : Structure L W}

/-- A source substructure embedded in C, together with an arbitrary labelling
of its vertices by elements of A. -/
structure QuotientBoundaryRequest
    (A : Structure L U) (C : Structure L W) where
  Carrier : Type v
  source : Structure L Carrier
  embedding : Embedding source C
  label : Carrier → U

namespace QuotientBoundaryRequest


/-- Build a quotient-boundary request from an embedded source and a label map. -/
def ofEmbedding
    {X : Type v} {R : Structure L X}
    (e : Embedding R C) (q : X → U) :
    QuotientBoundaryRequest A C where
  Carrier := X
  source := R
  embedding := e
  label := q

/-- Transport the source boundary through a full embedding. -/
def postcomp
    {X : Type v} {C' : Structure L X}
    (r : QuotientBoundaryRequest A C)
    (j : Embedding C C') :
    QuotientBoundaryRequest A C' where
  Carrier := r.Carrier
  source := r.source
  embedding := j.comp r.embedding
  label := r.label

end QuotientBoundaryRequest

/-- A quotient-labelled boundary is isolated when it is realized inside one
target A-copy and every source point landing in that target copy comes from
the boundary with exactly the recorded label. -/
def IsolatedQuotientBoundary
    (r : QuotientBoundaryRequest A C)
    (T : Structure L Y) (f : W → Y) : Prop :=
  ∃ targetCopy : Embedding A T,
    (∀ x, f (r.embedding x) = targetCopy (r.label x)) ∧
    IsFreeAmalgam.RootIsolated
      r.embedding targetCopy r.label f

namespace IsolatedQuotientBoundary

/-- Full homomorphisms cancel through a full target embedding. -/
theorem Embedding.cancel_homomorphism
    {X₀ X₁ X₂ : Type v}
    {A₀ : Structure L X₀} {A₁ : Structure L X₁}
    {A₂ : Structure L X₂}
    (j : Embedding A₁ A₂) {g : X₀ → X₁}
    (h : A₀.IsHomomorphism A₂ (j ∘ g)) :
    A₀.IsHomomorphism A₁ g := by
  constructor
  · intro R x hx
    exact (j.map_rel_iff R (g ∘ x)).mp (h.1 R x hx)
  · intro F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have htarget :
          j (g z) ∈ A₂.func F (j ∘ (g ∘ x)) := by
        have himg :
            (j ∘ g) z ∈
              imageSet (j ∘ g) (A₀.func F x) :=
          ⟨z, hz, rfl⟩
        have hm := h.2 F x
        rw [hm] at himg
        simpa [Function.comp_assoc] using himg
      have hj :
          j (g z) ∈ imageSet j (A₁.func F (g ∘ x)) := by
        rw [j.map_func F (g ∘ x)]
        exact htarget
      rcases hj with ⟨b, hb, hbeq⟩
      exact j.injective hbeq ▸ hb
    · intro hy
      have hj :
          j y ∈ A₂.func F (j ∘ (g ∘ x)) := by
        have himg :
            j y ∈ imageSet j (A₁.func F (g ∘ x)) :=
          ⟨y, hy, rfl⟩
        rw [j.map_func F (g ∘ x)] at himg
        exact himg
      have hj' :
          j y ∈ A₂.func F ((j ∘ g) ∘ x) := by
        simpa [Function.comp_assoc] using hj
      have hpre :
          j y ∈ imageSet (j ∘ g) (A₀.func F x) := by
        rw [h.2 F x]
        exact hj'
      rcases hpre with ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      apply j.injective
      exact hzy

/-- Any quotient labelling realized inside a full local completion is
necessarily a full homomorphism into the labelled control copy.  This is the
admissibility condition that distinguishes genuine quotient boundaries from a
raw weak part projection. -/
theorem label_isHomomorphism
    {r : QuotientBoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (hIso : IsolatedQuotientBoundary r T f)
    (hf : C.IsHomomorphism T f) :
    r.source.IsHomomorphism A r.label := by
  obtain ⟨targetCopy, hcompat, _⟩ := hIso
  have hcomp :
      r.source.IsHomomorphism T (f ∘ r.embedding) :=
    hf.comp r.embedding.isHomomorphism
  have heq :
      f ∘ r.embedding = targetCopy ∘ r.label := by
    funext x
    exact hcompat x
  rw [heq] at hcomp
  exact Embedding.cancel_homomorphism targetCopy hcomp


/-- With a homomorphism-embedding side witness, an isolated quotient label is
itself a homomorphism-embedding into A.  On every irreducible source piece,
the side witness supplies an actual embedding into the target; compatibility
puts its range inside the distinguished target A-copy, so it factors back
through that copy. -/
theorem label_isHomomorphismEmbedding
    {r : QuotientBoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (hIso : IsolatedQuotientBoundary r T f)
    (hf : C.IsHomomorphismEmbedding T f) :
    r.source.IsHomomorphismEmbedding A r.label := by
  have hLabelHom : r.source.IsHomomorphism A r.label :=
    label_isHomomorphism hIso hf.1
  obtain ⟨targetCopy, hcompat, _⟩ := hIso
  refine ⟨hLabelHom, ?_⟩
  intro X E hE e
  obtain ⟨g, hg⟩ :=
    hf.2 E hE (r.embedding.comp e)
  have hgrange :
      ∀ x : X, ∃ a : U, g x = targetCopy a := by
    intro x
    refine ⟨r.label (e x), ?_⟩
    calc
      g x = f (r.embedding (e x)) := hg x
      _ = targetCopy (r.label (e x)) :=
        hcompat (e x)
  let gA : Embedding E A :=
    g.factorThroughClosedRange targetCopy hgrange
  refine ⟨gA, ?_⟩
  intro x
  apply targetCopy.injective
  calc
    targetCopy (gA x) = g x :=
      Embedding.factorThroughClosedRange_spec
        g targetCopy hgrange x
    _ = f (r.embedding (e x)) := hg x
    _ = targetCopy (r.label (e x)) :=
      hcompat (e x)

/-- Isolation survives target postcomposition. -/
theorem postcompTarget
    {r : QuotientBoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (h : IsolatedQuotientBoundary r T f)
    {T' : Structure L Z} (j : Embedding T T') :
    IsolatedQuotientBoundary r T' (j ∘ f) := by
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

end IsolatedQuotientBoundary

/-- Projected quotient-boundary data: the boundary labels are compatible with
one full A-copy in the outer projection target D. -/
structure ProjectedQuotientBoundaryRequest
    {P : Type v}
    (A : Structure L U) (D : Structure L P)
    (C : Structure L W) (p : W → P)
    extends QuotientBoundaryRequest A C where
  beta : Embedding A D
  projection :
    ∀ x, p (embedding x) = beta (label x)

namespace ProjectedQuotientBoundaryRequest

/-- The tautological request supplied by a source embedding and a projection
whose values lie in a chosen A-copy. -/
def mkOfProjection
    {P X : Type v} {D : Structure L P} {R : Structure L X}
    {p : W → P}
    (e : Embedding R C)
    (q : X → U)
    (beta : Embedding A D)
    (hproj : ∀ x, p (e x) = beta (q x)) :
    ProjectedQuotientBoundaryRequest A D C p where
  Carrier := X
  source := R
  embedding := e
  label := q
  beta := beta
  projection := hproj

/-- Transport a projected quotient boundary through a source embedding
commuting with the projection. -/
def postcomp
    {P X : Type v} {D : Structure L P} {C' : Structure L X}
    {p : W → P} {p' : X → P}
    (r : ProjectedQuotientBoundaryRequest A D C p)
    (j : Embedding C C')
    (hcomm : ∀ x, p' (j x) = p x) :
    ProjectedQuotientBoundaryRequest A D C' p' where
  Carrier := r.Carrier
  source := r.source
  embedding := j.comp r.embedding
  label := r.label
  beta := r.beta
  projection := by
    intro x
    calc
      p' (j (r.embedding x)) = p (r.embedding x) := hcomm _
      _ = r.beta (r.label x) := r.projection x

end ProjectedQuotientBoundaryRequest

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

/-- A quotient-labelled boundary on the right side survives a compatible
functional lift. -/
theorem lift_preservesRightQuotientBoundary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G)
    (fL : E → TE) (fR : F → TF)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (r : QuotientBoundaryRequest A Right)
    (hr : IsolatedQuotientBoundary r TR fR) :
    let f :=
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
    IsolatedQuotientBoundary (r.postcomp iR) Target f := by
  classical
  obtain ⟨targetCopy, hsec, hsecIso⟩ := hr
  have hpersist :=
    functionalLiftMap_preservesRightRoot
      hSrc hTgt q fL fR hcompatL hcompatR hrootL
      r.embedding targetCopy r.label hsec hsecIso
  let f :=
    functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
  refine ⟨jR.comp targetCopy, ?_, ?_⟩
  · exact hpersist.1
  · exact hpersist.2

/-- Finite quotient-boundary diaries survive the same lift. -/
theorem lift_preservesRightQuotientDiary
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hTgt : IsFreeAmalgam tL tR jL jR)
    (q : H → G)
    (fL : E → TE) (fR : F → TF)
    (hcompatL : ∀ d, fL (sL d) = tL (q d))
    (hcompatR : ∀ d, fR (sR d) = tR (q d))
    (hrootL : RootIsolated sL tL q fL)
    (requests : List (QuotientBoundaryRequest A Right))
    (hDiary :
      ∀ r ∈ requests, IsolatedQuotientBoundary r TR fR) :
    let f :=
      functionalLiftMap hSrc hTgt q fL fR hcompatL hcompatR
    ∀ r ∈ requests,
      IsolatedQuotientBoundary (r.postcomp iR) Target f := by
  intro f r hr
  exact lift_preservesRightQuotientBoundary
    hSrc hTgt q fL fR hcompatL hcompatR hrootL
    r (hDiary r hr)

end IsFreeAmalgam

end StructuralRamsey.Structure
