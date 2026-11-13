import PartiteConstruction.Functional.WeakHistoryFreeTreeBasePower
import PartiteConstruction.Functional.WeakHistoryShadowCardinality

/-!
# Track D: exact weak small-image history-free strict functional witnesses

English first, including adversarial pure-side trace audit:
docs/track-d-historyfree-pure-trace-frontier-20261113.md

The no-history strict functional witness records only:
- a genuine strict FULL-functional Base-tree target;
- an ambient-relative weak HE on exactly the tested vertex set;
- FULL target A-copies protecting all ACTUAL ambient full A-copies.

The part map is irrelevant when the requested projected history is
the empty list, so it can be changed without any commuting diagram.

For ANY EHN source C→D, any literal weak finite source test S whose
EXACT projected image fits the old rank m pulls back a control
history-free strict functional tree witness on p[S], without
function-closure inflation or source-undefined-domain reflection.

We do NOT infer that a pure copied-side test with maximal projected
image protects NEW ambient A-copy traces crossing its attaching support.
That is the remaining pure-case compatibility gap for an unrestricted
native HJ history-free n-pass proof. The frozen survey is unchanged.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}} {UA VB X P Q : Type v}

/-- With EMPTY projected history, the part-label map is not part of
the actual strict weak-tree and ambient-copy witness. This is an
exact property-level change of unused bookkeeping, not a new target
map or a proof that labels are preserved by equality. -/
theorem changePart_noHistory
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L X} {part : X → P}
    {S : Set X}
    (h : SetAmbientRelativeWeakTreeWitness A Base C part S [])
    (part' : X → Q) :
    SetAmbientRelativeWeakTreeWitness A Base C part' S [] := by
  obtain ⟨Y, Target, hTree, f, hWeak, hCopies, _⟩ := h
  exact ⟨Y, Target, hTree, f, hWeak, hCopies,
    by intro K hK; cases hK⟩

/-- The literal projection image of an EXACT finite weak source test,
not its function-closed hull, is all the old rank-m control predecessor
needs for a strict history-free full-functional B-tree witness.

Every genuine ambient full irreducible A-copy is still protected,
using exactly the EHN irreducible-test clause. -/
theorem of_EHN_smallImage_noHistory
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L X} {D : Structure L P}
    {p : X → P} [DecidableEq P]
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hA : A.Irreducible)
    (m : ℕ)
    (hPrev : AtMostNoHistory A Base D (id : P → P) m)
    (S : Finset X)
    (hCard : (S.image p).card ≤ m) :
    SetAmbientRelativeWeakTreeWitness
      A Base C p (↑S : Set X) [] := by
  classical
  let I : Finset P := S.image p
  have hImage : (↑I : Set P) = p '' (↑S : Set X) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hControl :
      SetAmbientRelativeWeakTreeWitness
        A Base D (id : P → P) (p '' (↑S : Set X)) [] := by
    rw [← hImage]
    exact hPrev I hCard
  exact pullback_ehn hp hA (↑S : Set X) [] hControl

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB X Y P Q : Type v}

/-- With EMPTY history, AtMostNoHistory is intrinsic to the full
functional source and independent of the auxiliary part projection.
We do NOT assert any equality of projected parts on collapsed target
vertices: that false property is intentionally omitted. -/
theorem AtMostNoHistory.changePart
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L X} {p : X → P}
    {n : ℕ}
    (h : AtMostNoHistory A Base C p n)
    (p' : X → Q) :
    AtMostNoHistory A Base C p' n := by
  intro S hS
  exact (h S hS).changePart_noHistory p'

/-- Exact cardinal-monotone EHN pullback of the STRICT no-history
functional weak-tree invariant, retaining ambient A-copy protection.
The new source part map can be arbitrary because no label histories
are requested. This is stronger than part-commuting pullback ONLY
at this deliberately weak history-free level. -/
theorem AtMostNoHistory.pullback_ehn
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L X} {D : Structure L Y}
    [DecidableEq Y]
    (hA : A.Irreducible)
    (q : X → Y)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (pC : X → P) (pD : Y → Q)
    (n : ℕ)
    (hD : AtMostNoHistory A Base D pD n) :
    AtMostNoHistory A Base C pC n := by
  classical
  intro S hS
  let I : Finset Y := S.image q
  have hCard : I.card ≤ n :=
    (Finset.card_image_le).trans hS
  have hImage : (↑I : Set Y) = q '' (↑S : Set X) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hOld : SetAmbientRelativeWeakTreeWitness
      A Base D (id : Y → Y) (q '' (↑S : Set X)) [] := by
    have h := (hD I hCard).changePart_noHistory (id : Y → Y)
    rw [← hImage]
    exact h
  exact (pullback_ehn hq hA (↑S : Set X) [] hOld).changePart_noHistory pC

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
