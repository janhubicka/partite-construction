import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Ramsey arrows transfer through actual full part-preserving A/B copies

The 2019 local finite-completion endgame maps a sparse Ramsey picture
into a genuine target in K by a global (not necessarily injective)
homomorphism-embedding. Its Ramsey consequence needs no global full
embedding or domain reflection. It suffices that the chosen map
preserves every FULL controlled A and B copy as a genuine full
part-preserving Option(Set) embedding with the SAME vertex map.

This is a reusable genuine partial-function analogue of the checked
relational copywise Ramsey-transfer lemma. It preserves actual parts
of isolated vertices, exact complete function values and the
distinction undefined versus defined-empty along all lifted copies.
No weak carrier is closed or enlarged. Nothing is assumed about
how the copywise lifting certificates are obtained.

To apply this endgame to the corrected Appendix A class theorem,
one must still prove that the original functional local-completion
axiom supplies the required copywise lifts. This theorem does not
postulate such a class axiom.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {VA VB VC VD : Type w}

/-- A map of original vertex carriers protects every true FULL
part-preserving A and B subcopy; it need not be globally injective
nor reflect undefined function domains outside those copies. -/
def PartPreservingCopywiseCompletion
    (A : PartialSetStructure L VA) (partA : VA → P)
    (B : PartialSetStructure L VB) (partB : VB → P)
    (C : PartialSetStructure L VC) (partC : VC → P)
    (D : PartialSetStructure L VD) (partD : VD → P)
    (f : VC → VD) : Prop :=
  (∀ a : PartPreservingEmbedding A partA C partC,
    ∃ j : PartPreservingEmbedding A partA D partD,
      ∀ x, j.1.toFun x = f (a.1.toFun x)) ∧
  (∀ b : PartPreservingEmbedding B partB C partC,
    ∃ j : PartPreservingEmbedding B partB D partD,
      ∀ x, j.1.toFun x = f (b.1.toFun x))

/-- If the ACTUAL A/B copies of a sparse genuine partial-function
Ramsey witness survive in an actual target D on the same mapped
vertices, its genuine part-preserving Ramsey arrow survives too.
No arbitrary K-member normalization or intermediate strict
functional tree completion is needed for the arrow transfer. -/
theorem PartPreservingArrow.of_copywiseCompletion
    (A : PartialSetStructure L VA) (partA : VA → P)
    (B : PartialSetStructure L VB) (partB : VB → P)
    (C : PartialSetStructure L VC) (partC : VC → P)
    (D : PartialSetStructure L VD) (partD : VD → P)
    (κ : Type*)
    (hArrow : PartPreservingArrow A partA B partB C partC κ)
    (f : VC → VD)
    (hCopy : PartPreservingCopywiseCompletion
      A partA B partB C partC D partD f) :
    PartPreservingArrow A partA B partB D partD κ := by
  classical
  let liftA (a : PartPreservingEmbedding A partA C partC) :
      PartPreservingEmbedding A partA D partD :=
    Classical.choose (hCopy.1 a)
  have hliftA (a : PartPreservingEmbedding A partA C partC)
      (x : VA) :
      (liftA a).1.toFun x = f (a.1.toFun x) :=
    Classical.choose_spec (hCopy.1 a) x
  let liftB (b : PartPreservingEmbedding B partB C partC) :
      PartPreservingEmbedding B partB D partD :=
    Classical.choose (hCopy.2 b)
  have hliftB (b : PartPreservingEmbedding B partB C partC)
      (x : VB) :
      (liftB b).1.toFun x = f (b.1.toFun x) :=
    Classical.choose_spec (hCopy.2 b) x
  intro χ
  obtain ⟨b,hMono⟩ := hArrow (fun a => χ (liftA a))
  have hCompat (a : PartPreservingEmbedding A partA B partB) :
      liftA (b.comp a) = (liftB b).comp a := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    calc
      (liftA (b.comp a)).1.toFun x =
          f ((b.comp a).1.toFun x) :=
        hliftA (b.comp a) x
      _ = f (b.1.toFun (a.1.toFun x)) := rfl
      _ = (liftB b).1.toFun (a.1.toFun x) :=
        (hliftB b (a.1.toFun x)).symm
      _ = ((liftB b).comp a).1.toFun x := rfl
  refine ⟨liftB b, ?_⟩
  intro a1 a2
  rw [← hCompat a1, ← hCompat a2]
  exact hMono a1 a2

end StructuralRamsey.PartialSetStructure
