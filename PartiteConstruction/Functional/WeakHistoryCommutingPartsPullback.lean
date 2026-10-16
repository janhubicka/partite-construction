import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory

/-!
# Pull back strict functional weak-test witnesses along a compatible part projection

The previously verified small-image theorem pulls a strict B-tree
witness back through an EHN projection q:C→D when the witness's
projected-history carrier is the vertex set of D itself.

The actual native Hales–Jewett Picture has TWO projections:
  q : current functional stage → previous functional stage
  pC : current stage → original control Q
  pD : previous stage → original control Q
satisfying pC = pD ∘ q. Its inductive witness must retain
histories of the ORIGINAL control Q, not histories of the previous
stage's individual vertices.

This straightforward but important generalization proves exactly
that transfer, for every exact weak subset S. It uses the previously
validated ambient-relative EHN weak map pullback, then transports the
actual full A-copy embeddings and projected histories across q.
No source, image or root is enlarged by function closure.

In particular, if an actual ONE-LINE HJ binary attachment admits
the new EHN retraction q to Old, commuting with their part maps,
then the whole attachment inherits Old's strict full-functional
local weak-tree witness at the SAME vertex-size bound. Other line
attachments do not necessarily admit a COMMON retraction.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB W V P : Type v}

/-- EHN shadow pullback while preserving projected histories in a
SEPARATE original control P, provided the two stage projections
commute. This is the natural two-stage partite induction interface.

The source tests are exactly S and q[S]; all set-valued operation
images remain genuinely functional and no domain reflection is
needed. -/
theorem pullback_ehn_commutingParts
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x, pC x = pD (q x))
    (hA : A.Irreducible)
    (S : Set W) (history : List (Set P))
    (hD : SetAmbientRelativeWeakTreeWitness
      A Base D pD (q '' S) history) :
    SetAmbientRelativeWeakTreeWitness
      A Base C pC S history := by
  obtain ⟨Z, Target, hTree, g, hWeakD, hCopiesD, hHistD⟩ := hD
  let qS : S → q '' S :=
    fun x => ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
  let f : S → Z := g ∘ qS
  have hWeakC : IsAmbientRelativeWeakHE C S Target f :=
    hWeakD.pullback_ehn_exact hq S g
  have hCopiesC : SetAmbientACopyIntersections A C Target S f := by
    intro e
    obtain ⟨eD, heD⟩ := hq.2 A hA e
    obtain ⟨eT, hContained, hAgree⟩ := hCopiesD eD
    refine ⟨eT, hContained, ?_⟩
    intro a ha
    have hIn : eD a ∈ q '' S := by
      rw [heD a]
      exact ⟨e a, ha, rfl⟩
    calc
      eT a = g ⟨eD a, hIn⟩ := hAgree a hIn
      _ = f ⟨e a, ha⟩ := by
        change g (⟨eD a, hIn⟩ : q '' S) =
          g (qS ⟨e a, ha⟩)
        congr 1
        apply Subtype.ext
        exact heD a
  have hHistoryC : SetRespectsProjectedHistory pC S f history := by
    intro H hH x y hEq
    have hDxy := hHistD H hH (qS x) (qS y) hEq
    rw [hParts x.1, hParts y.1]
    exact hDxy
  exact ⟨Z, Target, hTree, f, hWeakC, hCopiesC, hHistoryC⟩

/-- A genuinely function-closed source test upgrades the same strict
target to an original-2019 partial-function homomorphism-embedding,
while retaining actual full ambient A intersections and original
control projected histories. -/
theorem pullback_ehn_commutingParts_closed
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x, pC x = pD (q x))
    (hA : A.Irreducible)
    (S : Set W) (hS : C.IsClosed S)
    (history : List (Set P))
    (hD : SetAmbientRelativeWeakTreeWitness
      A Base D pD (q '' S) history) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : S → Z,
        IsOriginalPartialHomomorphismEmbedding
          (C.induce S hS) Target f ∧
        SetAmbientACopyIntersections A C Target S f ∧
        SetRespectsProjectedHistory pC S f history :=
  (pullback_ehn_commutingParts
      pC pD q hq hParts hA S history hD).closed_test hS

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
