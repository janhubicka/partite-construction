import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.ProjectedHistoryFactor

/-!
# Marked A-copies are determined on the OCCUPIED projection labels

A fixed full alpha:A↪D mark is not safe for every weak test: the
two-edge path parity obstruction rules out the uniform protected-A
collar invariant. There is nevertheless a useful exact positive
statement already implicit in the VERIFIED weak-tree history witness.

For an exact weak test I⊆D, the ambient-full-A-copy certificate
extends the tested intersection with alpha to a genuine full
marked copy mark:A↪Target. If singleton projected histories are
also respected, then on all POSITIONS alpha(a) actually present in
I the mark is hit precisely by the tested point alpha(a).

We do NOT make assertions about target marks at alpha(a) outside I.
Those unoccupied boundary slots are precisely where the fixed-mark
parity obstruction and the unproved relative-history problem arise.

No closure of I, singleton-valued operation, total-fibre map or
artificial fixed global root is used. This is true with arbitrary
set-valued functions and strict FULL-functional target trees.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA VB P Z : Type v}

/-- An ordinary ambient-A intersection witness plus all singleton
histories gives a full embedded marked A-copy whose *occupied*
positions have an EXACT no-wrong-hit property. Unoccupied mark
vertices are intentionally uncontrolled. -/
theorem SetAmbientACopyIntersections.occupied_mark_trace
    {A : Structure L UA} {D : Structure L P}
    {Target : Structure L Z} {I : Set P}
    {f : I → Z} {history : List (Set P)}
    (hCopies : SetAmbientACopyIntersections A D Target I f)
    (hHist : SetRespectsProjectedHistory (id : P → P) I f history)
    (hSingletons : ∀ p : P, Set.singleton p ∈ history)
    (alpha : Embedding A D) :
    ∃ mark : Embedding A Target,
      mark.ContainedInIrreducible ∧
      (∀ (a : UA) (ha : alpha a ∈ I),
        mark a = f ⟨alpha a, ha⟩) ∧
      (∀ (x : I) (a : UA), alpha a ∈ I →
        (f x = mark a ↔ x.1 = alpha a)) := by
  obtain ⟨mark, hContained, hAgree⟩ := hCopies alpha
  refine ⟨mark, hContained, hAgree, ?_⟩
  intro x a ha
  constructor
  · intro hx
    let y : I := ⟨alpha a, ha⟩
    have hxy : f x = f y := hx.trans (hAgree a ha)
    have hh := hHist (Set.singleton x.1)
      (hSingletons x.1) x y hxy
    have hy : alpha a ∈ (Set.singleton x.1 : Set P) := by
      exact hh.mp (by simp)
    exact (Set.mem_singleton_iff.mp hy).symm
  · intro hx
    have hxeq : x = (⟨alpha a, ha⟩ : I) :=
      Subtype.ext hx
    rw [hxeq]
    exact (hAgree a ha).symm

/-- If the projected weak test already contains ALL alpha(A) labels,
the preceding occupied trace is a FULL exact protected mark. This is
a special-case extraction theorem, NOT a universal induction invariant. -/
theorem SetAmbientACopyIntersections.full_mark_trace_of_covered
    {A : Structure L UA} {D : Structure L P}
    {Target : Structure L Z} {I : Set P}
    {f : I → Z} {history : List (Set P)}
    (hCopies : SetAmbientACopyIntersections A D Target I f)
    (hHist : SetRespectsProjectedHistory (id : P → P) I f history)
    (hSingletons : ∀ p : P, Set.singleton p ∈ history)
    (alpha : Embedding A D)
    (hAll : ∀ a : UA, alpha a ∈ I) :
    ∃ mark : Embedding A Target,
      mark.ContainedInIrreducible ∧
      ∀ (x : I) (a : UA), f x = mark a ↔ x.1 = alpha a := by
  obtain ⟨mark, hContained, _hAgree, hTrace⟩ :=
    hCopies.occupied_mark_trace hHist hSingletons alpha
  exact ⟨mark, hContained, fun x a => hTrace x a (hAll a)⟩

end StructuralRamsey.Structure
