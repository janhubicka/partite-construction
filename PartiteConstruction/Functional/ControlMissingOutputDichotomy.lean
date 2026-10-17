import PartiteConstruction.Functional.WeakMissingRootCoherence
import PartiteConstruction.Functional.FibreExactness

/-!
# Control-missing functional output slots: source-undefined or source-omitted

The corrected native functional iterated Appendix A induction has to
distinguish the ambient active output masks on a genuine source partite
System from the active masks in its functional CONTROL. An EHN projection
is source-defined original-partial: source-undefined input tuples may
map to defined control tuples. Consequently not every missing CONTROL
slot is a missing AMBIENT source output slot.

For each exact weak S and each output part q, a missing CONTROL slot
has exactly two possible origins:
* PHANTOM: the ambient source fibre is empty and control q is active;
* OMITTED: the source is defined, q has a unique ambient source
  output, and that output lies outside S.

If S is function-closed, the omitted case is impossible; the
projection-defined/domain-reflection failure triggers the existing
reducible input-hull theorem. The hull is only a diagnostic; no test
is enlarged to its closure or counted with the wrong cardinality.

This is a semantic/root-geometry reduction, not the unproved
history-compatible strict B-tree target completion.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- The control has an actual output at part q, but the EXACT weak
source test retains no output in that part.

Unlike the source missing-slot predicate, this can happen even when
the source function is entirely undefined at these inputs. -/
def System.ControlMissingAtPart
    (B : System L P V) (D : Structure L P) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (q : P) : Prop :=
  q ∈ D.func F (B.part ∘ (Subtype.val ∘ xs)) ∧
    ¬ (B.weakInduce S).ActiveOutputAtPart F xs q

/-- A phantom control slot: the control has this output but the
AMBIENT source fibre is empty, so there is no source output to
retain or omit. This is allowed by original-2019 EHN projections. -/
def System.ProjectedUndefinedAtPart
    (B : System L P V) (D : Structure L P) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (q : P) : Prop :=
  ¬ (B.func F (Subtype.val ∘ xs)).Nonempty ∧
    q ∈ D.func F (B.part ∘ (Subtype.val ∘ xs))

/-- EXACT EHN dichotomy for an absent weak output part.

If the ambient source has any function output, EHN fibre exactness
lifts the specified control output q to a source output of part q;
if that output is not in the weak test, it is an omitted source
root slot. The only other possibility is an entirely undefined
source input whose projection is defined in the control. -/
theorem System.controlMissing_iff_undefined_or_omitted
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V) (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P) :
    B.ControlMissingAtPart D S F xs q ↔
      B.ProjectedUndefinedAtPart D S F xs q ∨
      B.MissingActiveOutputAtPart S F xs q := by
  constructor
  · rintro ⟨hControl, hWeakMissing⟩
    by_cases hDefined :
        (B.func F (Subtype.val ∘ xs)).Nonempty
    · have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part :=
        hB
      have hExact :=
        hp.map_func_of_nonempty F (Subtype.val ∘ xs) hDefined
      have hLift : q ∈
          imageSet B.part (B.func F (Subtype.val ∘ xs)) := by
        rw [hExact]
        exact hControl
      obtain ⟨y, hy, hq⟩ := hLift
      exact Or.inr ⟨⟨y, hy, hq⟩, hWeakMissing⟩
    · exact Or.inl ⟨hDefined, hControl⟩
  · intro h
    rcases h with hPhantom | hOmitted
    · refine ⟨hPhantom.2, ?_⟩
      rintro ⟨y, hy, _hyPart⟩
      exact hPhantom.1 ⟨y.1, hy⟩
    · obtain ⟨⟨y, hy, hq⟩, hNo⟩ := hOmitted
      have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part :=
        hB
      have hyD :
          B.part y ∈ D.func F (B.part ∘ (Subtype.val ∘ xs)) :=
        hp.1.2 F (Subtype.val ∘ xs) y hy
      refine ⟨?_, hNo⟩
      rw [hq] at hyD
      exact hyD

/-- The two possible EHN defects are DISJOINT: an omitted source
value witnesses a nonempty ambient source fibre. -/
theorem System.projectedUndefined_not_missingActive
    (B : System L P V) (D : Structure L P) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P)
    (h : B.ProjectedUndefinedAtPart D S F xs q) :
    ¬ B.MissingActiveOutputAtPart S F xs q := by
  rintro ⟨⟨y, hy, _⟩, _⟩
  exact h.1 ⟨y, hy⟩

/-- On a GENUINELY function-closed weak set there are no omitted
ambient source values. Missing control slots are PRECISELY the
genuine EHN domain-reflection failures; function-closedness of S
does not exclude those failures. -/
theorem System.controlMissing_of_closed_iff_projectedUndefined
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V) (hClosed : B.toStructure.IsClosed S)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P) :
    B.ControlMissingAtPart D S F xs q ↔
      B.ProjectedUndefinedAtPart D S F xs q := by
  constructor
  · intro hControl
    rcases (B.controlMissing_iff_undefined_or_omitted
      D hB S F xs q).mp hControl with hPhantom | hOmitted
    · exact hPhantom
    · exact False.elim
        (((B.isClosed_iff_noMissingActiveOutputs S).mp hClosed)
          F xs q hOmitted)
  · intro hPhantom
    exact (B.controlMissing_iff_undefined_or_omitted
      D hB S F xs q).mpr (Or.inl hPhantom)

/-- A missing control slot in a closed weak source test forces
a PROPER full functional free decomposition of the original
SOURCE input-generated closure hull.

The hull is used ONLY to diagnose reducibility. The exact weak S
remains untouched, and the induction is still on its vertex count. -/
theorem System.controlMissing_closed_inputHull_reducible
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V) (hClosed : B.toStructure.IsClosed S)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P)
    (hControl : B.ControlMissingAtPart D S F xs q) :
    Nonempty
      (ProperFreeDecomposition
        (B.toStructure.induce
          (B.toStructure.functionClosure
            (Set.range (Subtype.val ∘ xs)))
          (B.toStructure.functionClosure_isClosed
            (Set.range (Subtype.val ∘ xs))))) := by
  have hPhantom : B.ProjectedUndefinedAtPart D S F xs q :=
    (B.controlMissing_of_closed_iff_projectedUndefined
      D hB S hClosed F xs q).mp hControl
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part :=
    hB
  exact hp.inputHull_reducible_of_domainFailure
    F (Subtype.val ∘ xs) ⟨q, hPhantom.2⟩ hPhantom.1

/-- When the ambient source is defined, an EHN control-missing
slot is realized by exactly one source output of part q OUTSIDE
the exact weak test. This is the coherent missing source mask
handled by the common-root preimage lemmas. -/
theorem System.controlMissing_defined_uniqueOutside
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (q : P)
    (hDefined : (B.func F (Subtype.val ∘ xs)).Nonempty)
    (hControl : B.ControlMissingAtPart D S F xs q) :
    ∃! y : V,
      y ∈ B.func F (Subtype.val ∘ xs) ∧
      B.part y = q ∧ y ∉ S := by
  rcases (B.controlMissing_iff_undefined_or_omitted
    D hB S F xs q).mp hControl with hPhantom | hOmitted
  · exact False.elim (hPhantom.1 hDefined)
  · exact B.missingActiveOutputAtPart_uniqueOutside
      S F xs q hOmitted

end StructuralRamsey.FunctionalPartite
