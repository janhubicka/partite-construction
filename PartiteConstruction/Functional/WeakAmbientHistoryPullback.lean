import PartiteConstruction.Functional.AmbientACopyOriginalPartialHistory
import PartiteConstruction.Functional.WeakSingletonOriginalPartialInclusion
import PartiteConstruction.Functional.AmbientWeakPartialProjection

/-!
# Exact weak-image pullback of strict functional B-tree witnesses

This is the SMALL-PROJECTED-IMAGE half of the published functional
iterated partite induction, stated with the corrected weak/ambient
projection invariant. No relational tree replaces the functional
target: every witness is a genuine strict full-functional B-tree.

A weak test retains EXACTLY its vertices. Its original-partial map
preserves complete surviving singleton-valued function fibres and
protects every full ambient irreducible piece with range inside
the weak test. We also track intersections of the test with ACTUAL
full ambient A-copies and arbitrary projected history diaries.

A predecessor tree witness for the EXACT weak projected image p[S]
pulls back along the EHN projection. Neither source nor target needs
to be function-closed. If the source test S itself IS closed, the
ambient-relative weak map upgrades to a genuine original-partial
homomorphism-embedding into the same strict functional B-tree.

This proves a conditional small-image transfer and the rank-zero
initial case; it does not prove that mixed Hales-Jewett attachments
preserve the weak witness invariant at maximal projected rank.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U VB W P : Type v}

/-- A strict full-functional B-tree witness for an EXACT weak vertex
test, with both ambient-irreducible protection and genuine full
ambient A-copy intersections, plus projected history. Weak test sets
are not replaced by their function-closed hulls. -/
def FunctionalWeakAmbientProjectedTreeWitness
    (A : Structure L U) (Base : Structure L VB)
    (C : Structure L W) (p : W → P)
    (S : Finset W) (history : List (Set P)) : Prop :=
  ∃ (Z : Type v) (Target : Structure L Z),
    TreeAmalgam Base Z Target ∧
    ∃ f : ↥(↑S : Set W) → Z,
      IsAmbientWeakOriginalPartialHE C (↑S : Set W) Target f ∧
      FunctionalAmbientACopyIntersections
        (A := A) (C := C) (Target := Target) S f ∧
      FunctionalRespectsProjectedHistory p S f history

namespace FunctionalWeakAmbientProjectedTreeWitness

/-- For genuinely CLOSED S the corrected weak witness gives the
required ordinary original-2019 homomorphism-embedding into its
actual strict B-tree target; no extra vertices or closure hull. -/
theorem closed_completion
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {p : W → P}
    {S : Finset W} {history : List (Set P)}
    (h : FunctionalWeakAmbientProjectedTreeWitness
      A Base C p S history)
    (hClosed : C.IsClosed (↑S : Set W)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : ↥(↑S : Set W) → Z,
        IsOriginalPartialHomomorphismEmbedding
          (C.induce (↑S : Set W) hClosed) Target f ∧
        FunctionalAmbientACopyIntersections
          (A := A) (C := C) (Target := Target) S f ∧
        FunctionalRespectsProjectedHistory p S f history := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩ := h
  exact ⟨Z, Target, hTree, f,
    hWeak.toOriginalPartialHE_of_closed hClosed, hCopies, hHist⟩

/-- Every strict singleton-valued functional B-tree is an
unrestricted weak-tree witness for every finite test and EVERY
history list. The weak inclusion is original-partial on retained
singleton fibres and remains full on actual ambient irreducibles.
Only irreducibility of A and B is needed to locate A-copies inside B. -/
theorem of_tree_singleton
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W}
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (hTree : TreeAmalgam Base W C)
    (hSingle : C.SingletonValued)
    (p : W → P) (S : Finset W) (history : List (Set P)) :
    FunctionalWeakAmbientProjectedTreeWitness
      A Base C p S history := by
  let inc : ↥(↑S : Set W) → W := Subtype.val
  have hWeak : IsAmbientWeakOriginalPartialHE
      C (↑S : Set W) C inc := by
    constructor
    · exact hSingle.weakInclusion_originalPartial (↑S : Set W)
    · intro X E _hE e _he
      exact ⟨e, fun _ => rfl⟩
  refine ⟨W, C, hTree, inc, hWeak, ?_, ?_⟩
  · intro e
    obtain ⟨baseCopy, hContains⟩ :=
      (LooseTreeAmalgam.ofTree hTree).irreducible_contained_in_copy hA e
    refine ⟨e, ?_, ?_⟩
    · exact ⟨VB, Base, hBase, baseCopy, hContains⟩
    · intro a _ha
      rfl
  · intro H _hH x y hxy
    have heq : x = y := Subtype.val_injective hxy
    subst y
    exact Iff.rfl

/-- Pull back a strict functional weak-tree witness of the PRECISE
projected weak vertex set through an EHN projection from a
singleton-valued source. Retains genuine ambient A-copy intersections
and every finite projected-history predicate.

This theorem does not assert the predecessor witness's existence.
In an iterated partite proof that is supplied at the smaller
projected rank by the induction hypothesis. -/
theorem pullback_ehn
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L P}
    {p : W → P}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hSingle : C.SingletonValued)
    (hA : A.Irreducible)
    (S : Finset W) (I : Finset P)
    (hI : (↑I : Set P) = p '' (↑S : Set W))
    (history : List (Set P))
    (hD : FunctionalWeakAmbientProjectedTreeWitness
      A Base D (id : P → P) I history) :
    FunctionalWeakAmbientProjectedTreeWitness
      A Base C p S history := by
  obtain ⟨Z, Target, hTree, g, hWeakD, hCopiesD, hHistD⟩ := hD
  have hRange : ∀ x : ↥(↑S : Set W), p x.1 ∈ (↑I : Set P) := by
    intro x
    rw [hI]
    exact ⟨x.1, x.2, rfl⟩
  let pS : ↥(↑S : Set W) → ↥(↑I : Set P) :=
    fun x => ⟨p x.1, hRange x⟩
  have hpWeak : IsOriginalPartialHomomorphism
      (C.weakInduce (↑S : Set W))
      (D.weakInduce (↑I : Set P)) pS :=
    hp.toOriginalPartial.1.weakImage_singleton_toSet
      hSingle (↑S : Set W) (↑I : Set P) hRange
  let f : ↥(↑S : Set W) → Z := g ∘ pS
  have hHom : IsOriginalPartialHomomorphism
      (C.weakInduce (↑S : Set W)) Target f :=
    hWeakD.1.comp hpWeak
  have hWeakC : IsAmbientWeakOriginalPartialHE
      C (↑S : Set W) Target f := by
    refine ⟨hHom, ?_⟩
    intro X E hE e he
    obtain ⟨eD, heD⟩ := hp.2 E hE e
    have heDI : ∀ x : X, eD x ∈ (↑I : Set P) := by
      intro x
      rw [heD x]
      exact hRange ⟨e x, he x⟩
    obtain ⟨eT, heT⟩ := hWeakD.2 E hE eD heDI
    refine ⟨eT, ?_⟩
    intro x
    calc
      eT x = g ⟨eD x, heDI x⟩ := heT x
      _ = f ⟨e x, he x⟩ := by
        change g (⟨eD x, heDI x⟩ : ↥(↑I : Set P)) =
          g (pS ⟨e x, he x⟩)
        congr 1
        apply Subtype.ext
        exact heD x
  have hCopiesC : FunctionalAmbientACopyIntersections
      (A := A) (C := C) (Target := Target) S f := by
    intro e
    obtain ⟨eD, heD⟩ := hp.2 A hA e
    obtain ⟨eT, hIrred, hAgree⟩ := hCopiesD eD
    refine ⟨eT, hIrred, ?_⟩
    intro a ha
    have haI : eD a ∈ (↑I : Set P) := by
      rw [heD a]
      exact hRange ⟨e a, ha⟩
    calc
      eT a = g ⟨eD a, haI⟩ := hAgree a haI
      _ = f ⟨e a, ha⟩ := by
        change g (⟨eD a, haI⟩ : ↥(↑I : Set P)) =
          g (pS ⟨e a, ha⟩)
        congr 1
        apply Subtype.ext
        exact heD a
  have hHistC : FunctionalRespectsProjectedHistory
      p S f history := by
    intro H hH x y hxy
    exact hHistD H hH (pS x) (pS y) hxy
  exact ⟨Z, Target, hTree, f, hWeakC, hCopiesC, hHistC⟩

/-- The small-image branch with its actual finite image. The size
bound is never evaluated on the function-closed hull; when the
projected image has <n points the predecessor rank-(n-1) witness
supplies the strict full-functional tree completion. -/
theorem pullback_smaller_projected_image
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L P}
    {p : W → P} [DecidableEq P]
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hSingle : C.SingletonValued)
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : ∀ I : Finset P, I.card < n →
      ∀ history : List (Set P),
        FunctionalWeakAmbientProjectedTreeWitness
          A Base D (id : P → P) I history)
    (S : Finset W) (hSmall : (S.image p).card < n)
    (history : List (Set P)) :
    FunctionalWeakAmbientProjectedTreeWitness
      A Base C p S history := by
  have hI : (↑(S.image p) : Set P) =
      p '' (↑S : Set W) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact pullback_ehn hp hSingle hA S (S.image p) hI
    history (hD (S.image p) hSmall history)

end FunctionalWeakAmbientProjectedTreeWitness

end StructuralRamsey.Structure
