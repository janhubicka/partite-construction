import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue
import PartiteConstruction.Functional.WeakHistoryCommutingPartsPullback

/-!
# Exact weak-image transfer for protected A-collar witnesses

An exploratory, conditional functional Appendix A invariant equips strict
full-functional B-tree witnesses with an EXACT protected marked A-copy.
This module records that witness as a reusable predicate and proves
the SMALL PROJECTED IMAGE branch: it pulls back along any EHN
homomorphism-embedding q:C→D commuting with control part maps.

The selected finite weak test S and its exact weak image q[S] are
unchanged. Neither is enlarged to its generated function-closure.
All genuinely multivalued function fibres use the established
ambient-relative weak HE, never a fictitious global total-fibre map.

A protected predecessor mark is the SAME FULL marked A embedding
after pullback, since exact projected labels commute with q. The
A-copy intersection data and finite projected histories also transfer.
On a genuinely closed test, the exact weak witness upgrades to an
original-2019 partial homomorphism-embedding into the same strict
functional tree.

This proves a valid SMALL-IMAGE transfer conditional on a predecessor
protected witness. The arbitrary initial-stage protected-witness
premise is FALSE (parity obstruction: ProtectedAMarkParityObstruction).
Consequently this is reusable relative infrastructure, NOT a
complete or viable unrestricted Appendix A induction by itself.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA VB W V P : Type v}

/-- A strict full-functional Base-tree weak-test witness with an
exact protected full A-collar in the target, actual ambient-A-copy
control, and arbitrary projected history.

This witness does not demand a global EHN label map on every target
vertex. Existence of such a marked witness at arbitrary weak test
sets is NOT an automatic consequence of strict B-tree completion. -/
def SetAmbientProtectedWeakTreeWitness
    (A : Structure L UA) (Base : Structure L VB)
    {Control : Structure L P} (alpha : Embedding A Control)
    (C : Structure L W) (p : W → P)
    (S : Set W) (history : List (Set P)) : Prop :=
  ∃ (Z : Type v) (Target : Structure L Z),
    TreeAmalgam Base Z Target ∧
    ∃ f : S → Z,
      IsAmbientRelativeWeakHE C S Target f ∧
      SetAmbientACopyIntersections A C Target S f ∧
      SetRespectsProjectedHistory p S f history ∧
      ∃ mark : Embedding A Target,
        mark.ContainedInIrreducible ∧
        ProtectedAMark alpha p S f mark

namespace SetAmbientProtectedWeakTreeWitness

/-- Forget only the protected marked collar; retain the same exact
weak test, strict functional target and ambient/projected histories. -/
theorem toWeak
    {A : Structure L UA} {Base : Structure L VB}
    {Control : Structure L P} {alpha : Embedding A Control}
    {C : Structure L W} {p : W → P}
    {S : Set W} {history : List (Set P)}
    (h : SetAmbientProtectedWeakTreeWitness
      A Base alpha C p S history) :
    SetAmbientRelativeWeakTreeWitness A Base C p S history := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist, _mark, _hMark, _hTrace⟩ := h
  exact ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩

/-- On a function-closed tested vertex set, the same target becomes
a strict original-2019 partial-function completion, still carrying
the protected A-collar and arbitrary projected histories. -/
theorem closed_test
    {A : Structure L UA} {Base : Structure L VB}
    {Control : Structure L P} {alpha : Embedding A Control}
    {C : Structure L W} {p : W → P}
    {S : Set W} {history : List (Set P)}
    (h : SetAmbientProtectedWeakTreeWitness
      A Base alpha C p S history)
    (hClosed : C.IsClosed S) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : S → Z,
        IsOriginalPartialHomomorphismEmbedding
          (C.induce S hClosed) Target f ∧
        SetAmbientACopyIntersections A C Target S f ∧
        SetRespectsProjectedHistory p S f history ∧
        ∃ mark : Embedding A Target,
          mark.ContainedInIrreducible ∧
          ProtectedAMark alpha p S f mark := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist, mark, hc, hTrace⟩ := h
  exact ⟨Z, Target, hTree, f,
    hWeak.toOriginalPartialHE_of_closed hClosed,
    hCopies, hHist, mark, hc, hTrace⟩

/-- Exact-image pullback of a protected collar through an EHN shadow
commuting with a separate fixed control part map.

Crucially the protected iff is pointwise preserved, with no assumption
that the projected weak image is function-closed or that q is
injective/reflects undefined function domains. -/
theorem pullback_ehn_commutingParts
    {A : Structure L UA} {Base : Structure L VB}
    {Control : Structure L P} (alpha : Embedding A Control)
    {C : Structure L W} {D : Structure L V}
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x, pC x = pD (q x))
    (hA : A.Irreducible)
    (S : Set W) (history : List (Set P))
    (hD : SetAmbientProtectedWeakTreeWitness
      A Base alpha D pD (q '' S) history) :
    SetAmbientProtectedWeakTreeWitness
      A Base alpha C pC S history := by
  classical
  obtain ⟨Z, Target, hTree, g, hWeakD, hCopiesD, hHistD,
      mark, hContained, hTraceD⟩ := hD
  let qS : S → q '' S :=
    fun x => ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
  let f : S → Z := g ∘ qS
  have hWeakC : IsAmbientRelativeWeakHE C S Target f :=
    hWeakD.pullback_ehn_exact hq S g
  have hCopiesC : SetAmbientACopyIntersections A C Target S f := by
    intro e
    obtain ⟨eD, heD⟩ := hq.2 A hA e
    obtain ⟨eT, hContains, hAgrees⟩ := hCopiesD eD
    refine ⟨eT, hContains, ?_⟩
    intro a ha
    have haD : eD a ∈ q '' S := by
      rw [heD a]
      exact ⟨e a, ha, rfl⟩
    calc
      eT a = g ⟨eD a, haD⟩ := hAgrees a haD
      _ = f ⟨e a, ha⟩ := by
        change g (⟨eD a, haD⟩ : q '' S) =
          g (qS ⟨e a, ha⟩)
        congr 1
        apply Subtype.ext
        exact heD a
  have hHistC : SetRespectsProjectedHistory pC S f history := by
    intro H hH x y hEq
    have hOld := hHistD H hH (qS x) (qS y) hEq
    change pD (q x.1) ∈ H ↔ pD (q y.1) ∈ H at hOld
    rw [hParts x.1, hParts y.1]
    exact hOld
  have hTraceC : ProtectedAMark alpha pC S f mark := by
    intro x a
    constructor
    · intro hHit
      calc
        pC x.1 = pD (q x.1) := hParts x.1
        _ = alpha a := (hTraceD (qS x) a).1 hHit
    · intro hLabel
      have hLabelD : pD (q x.1) = alpha a :=
        (hParts x.1).symm.trans hLabel
      exact (hTraceD (qS x) a).2 hLabelD
  exact ⟨Z, Target, hTree, f, hWeakC, hCopiesC, hHistC,
    mark, hContained, hTraceC⟩

end SetAmbientProtectedWeakTreeWitness

/-- The protected weak-test property for every EXACT finite vertex
subset of size at most n. The rank counts tested vertices, not
generated hulls or preimages. -/
def AtMostProtectedWeakTreeWitness
    (A : Structure L UA) (Base : Structure L VB)
    {Control : Structure L P} (alpha : Embedding A Control)
    (C : Structure L W) (p : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ history : List (Set P),
      SetAmbientProtectedWeakTreeWitness
        A Base alpha C p (↑S : Set W) history

namespace AtMostProtectedWeakTreeWitness

/-- The rank-n protected invariant pulls back along an EHN shadow
without increasing the number of vertices in the exact projected
weak test; projected image cardinality is bounded by source size. -/
theorem pullback_ehn_commutingParts
    {A : Structure L UA} {Base : Structure L VB}
    {Control : Structure L P} (alpha : Embedding A Control)
    {C : Structure L W} {D : Structure L V}
    [DecidableEq V]
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x, pC x = pD (q x))
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : AtMostProtectedWeakTreeWitness A Base alpha D pD n) :
    AtMostProtectedWeakTreeWitness A Base alpha C pC n := by
  intro S hS history
  let I : Finset V := S.image q
  have hImage : (↑I : Set V) = q '' (↑S : Set W) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hICard : I.card ≤ n :=
    (Finset.card_image_le).trans hS
  have hOld : SetAmbientProtectedWeakTreeWitness
      A Base alpha D pD (q '' (↑S : Set W)) history := by
    have hTmp := hD I hICard history
    rw [hImage] at hTmp
    exact hTmp
  exact SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts
    alpha pC pD q hq hParts hA (↑S : Set W) history hOld

end AtMostProtectedWeakTreeWitness

end StructuralRamsey.Structure
