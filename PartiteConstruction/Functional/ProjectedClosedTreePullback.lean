import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Functional.GeneratedTreeCompletion

/-! # Closed-image transfer of strict functional tree completions

The native EHN iteration controls the size of the tested vertex set, not
the size of its function closure. For a *closed* test whose projection is a
full function homomorphism-embedding, its projected image is automatically
closed. Thus a previous-stage strict B-tree completion on the projected
image can be pulled back without enlarging the source test.

This lemma handles the small-projected-image case. It does not settle the
mixed case where the projection is injective on the test and the common
separator is reducible. -/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {VB W P : Type v}
variable {Base : Structure L VB} {C : Structure L W}
variable {D : Structure L P}
variable [DecidableEq P]
variable {m : ℕ}

/-- A locally full projection of a closed test allows the strict functional
tree completion of its projected closed image to be pulled back. The image
size, not the source closure hull, is the only rank charged to the
previous-stage completion. -/
theorem LocallyClosedTreeCompletable.pullback_localFull_closedImage
    (hD : LocallyClosedTreeCompletable Base D m)
    (p : W → P)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hpS :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding D
        (p ∘ Subtype.val))
    (hImage : (S.image p).card ≤ m) :
    HasTreeCompletion Base (C.induce (↑S : Set W) hS) := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let q : ↥(↑S : Set W) → P := p ∘ Subtype.val
  have hqIHE : Small.IsHomomorphismEmbedding D q := hpS
  have hqHom : Small.IsHomomorphism D q := hqIHE.1

  let I : Finset P := S.image p
  have hrange : Set.range q = (↑I : Set P) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hxS, hxy⟩
      let xs : ↥(↑S : Set W) := ⟨x, hxS⟩
      exact ⟨xs, hxy⟩
  have hIclosed : D.IsClosed (↑I : Set P) := by
    rw [← hrange]
    exact hqHom.range_isClosed
  let R := D.induce (↑I : Set P) hIclosed
  let incR : Embedding R D :=
    inclusion D (↑I : Set P) hIclosed
  let qR : ↥(↑S : Set W) → ↥(↑I : Set P) :=
    fun x => ⟨q x, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩

  have hqRHom : Small.IsHomomorphism R qR :=
    hqHom.codRestrict (↑I : Set P) hIclosed
      (fun x => Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩)
  have hqRIHE : Small.IsHomomorphismEmbedding R qR := by
    refine ⟨hqRHom, ?_⟩
    intro X E hE e
    obtain ⟨g, hg⟩ := hqIHE.2 E hE e
    have hgrange :
        ∀ z : X, ∃ r : ↥(↑I : Set P), g z = incR r := by
      intro z
      let r : ↥(↑I : Set P) :=
        ⟨q (e z), Finset.mem_image.mpr
          ⟨(e z).1, (e z).2, rfl⟩⟩
      exact ⟨r, hg z⟩
    let gr : Embedding E R :=
      g.factorThroughClosedRange incR hgrange
    refine ⟨gr, ?_⟩
    intro z
    apply Subtype.ext
    have hfactor :
        incR (gr z) = g z :=
      Embedding.factorThroughClosedRange_spec g incR hgrange z
    calc
      (gr z).1 = g z := hfactor
      _ = q (e z) := hg z
      _ = (qR (e z)).1 := rfl

  obtain ⟨Z, Target, hTree, f, hf⟩ :=
    hD I hImage hIclosed
  exact ⟨Z, Target, hTree, f ∘ qR, hf.comp hqRIHE⟩

/-- An EHN projection restricted to a closed test becomes full if function
domains reflect there, so the projected-size transfer applies. -/
theorem LocallyClosedTreeCompletable.pullback_EHN_closedImage_of_domainReflection
    (hD : LocallyClosedTreeCompletable Base D m)
    {p : W → P}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hImage : (S.image p).card ≤ m)
    (hreflect :
      ∀ F (x : Fin (L.funcArity F) → ↥(↑S : Set W)),
        (D.func F ((p ∘ Subtype.val) ∘ x)).Nonempty →
          ((C.induce (↑S : Set W) hS).func F x).Nonempty) :
    HasTreeCompletion Base (C.induce (↑S : Set W) hS) := by
  have hpS :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding D
        (p ∘ Subtype.val) :=
    hp.restrictClosed_toFull_of_domainReflection
      (↑S : Set W) hS hreflect
  exact hD.pullback_localFull_closedImage p S hS hpS hImage

end StructuralRamsey.Structure
