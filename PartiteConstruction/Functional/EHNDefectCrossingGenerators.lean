import PartiteConstruction.Functional.EHNGlobalDefectDecomposition

/-!
# Track D: actual original input generators cross BOTH sides of a defect hull

The preceding source-decomposition trichotomy gives a proper full native
free decomposition of the full function-closed input hull of any relation
reflection or function-domain defect.  Here we strengthen that statement:
EVERY such proper decomposition has a particular ORIGINAL input generator
absent from its left side, and another actual input generator absent
from its right side.

In particular an input-tuple defect cannot be explained by one proper
source side which already contains all input generators.  The proof
respects the actual generated full native hull, including all
set-valued function outputs, nullaries and repeated inputs.  It
does not change the literal weak Hales--Jewett tested set.

This is a source-side crossing certificate, NOT the history-compatible
relative strict B-tree extension missing from Appendix A.
-/

namespace StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {U V : Type v} {I : Type w}

/-- The ORIGINAL named input generators of a full function-closed hull
must cross BOTH sides of any proper full-functional free
decomposition of that hull. The two missing indices may differ.

This does not assert that the entire original test splits in the
same fashion; only the diagnostic native input hull is decomposed. -/
theorem ProperFreeDecomposition.crossedInputGenerators
    (C : Structure L U)
    (xs : I → U)
    (d : ProperFreeDecomposition
      (C.induce (C.functionClosure (Set.range xs))
        (C.functionClosure_isClosed (Set.range xs)))) :
    let H := C.functionClosure (Set.range xs)
    let q : I → H := fun i =>
      ⟨xs i, C.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
    (∃ i : I, q i ∉ Set.range d.leftIn) ∧
      (∃ i : I, q i ∉ Set.range d.rightIn) := by
  classical
  let H : Set U := C.functionClosure (Set.range xs)
  let hH : C.IsClosed H := C.functionClosure_isClosed (Set.range xs)
  let Small := C.induce H hH
  let q : I → H := fun i =>
    ⟨xs i, C.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
  change (∃ i : I, q i ∉ Set.range d.leftIn) ∧
    (∃ i : I, q i ∉ Set.range d.rightIn)
  have hQGen :
      ∀ T : Set H, Small.IsClosed T →
        (∀ i : I, q i ∈ T) → ∀ z : H, z ∈ T := by
    intro T hT hqT z
    let T0 : Set U :=
      {a | ∃ ha : a ∈ H, (⟨a, ha⟩ : H) ∈ T}
    have hT0 : C.IsClosed T0 := by
      intro Func args hargs out hout
      let argsH : Fin (L.funcArity Func) → H :=
        fun i => ⟨args i, (hargs i).choose⟩
      have hargsT : ∀ i, argsH i ∈ T :=
        fun i => (hargs i).choose_spec
      have houtH : out ∈ H :=
        hH Func args (fun i => (hargs i).choose) hout
      have houtIn : (⟨out, houtH⟩ : H) ∈ Small.func Func argsH := by
        change out ∈ C.func Func (Subtype.val ∘ argsH)
        have hargsEq : Subtype.val ∘ argsH = args := by
          funext i
          rfl
        rw [hargsEq]
        exact hout
      exact ⟨houtH, hT Func argsH hargsT houtIn⟩
    have hInputs : Set.range xs ⊆ T0 := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(q i).2, hqT i⟩
    exact (z.2 T0 hT0 hInputs).2
  have hNotLeft : ¬ ∀ i : I, q i ∈ Set.range d.leftIn := by
    intro hAll
    apply d.leftProper
    intro z
    exact hQGen (Set.range d.leftIn) d.leftIn.range_isClosed hAll z
  have hNotRight : ¬ ∀ i : I, q i ∈ Set.range d.rightIn := by
    intro hAll
    apply d.rightProper
    intro z
    exact hQGen (Set.range d.rightIn) d.rightIn.range_isClosed hAll z
  push_neg at hNotLeft hNotRight
  exact ⟨hNotLeft, hNotRight⟩

/-- A surplus TARGET relation on an ACTUAL source input tuple
identifies an input that crosses each side of one genuine
proper FULL free decomposition of the original generated hull. -/
theorem IsEHNHomomorphismEmbedding.relationFailure_crossesSourceGenerators
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (R : L.RelSymbol) (xs : Fin (L.relArity R) → U)
    (hTarget : D.rel R (p ∘ xs))
    (hSource : ¬ C.rel R xs) :
    let H := C.functionClosure (Set.range xs)
    let q : Fin (L.relArity R) → H := fun i =>
      ⟨xs i, C.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
    ∃ d : ProperFreeDecomposition
        (C.induce H (C.functionClosure_isClosed (Set.range xs))),
      (∃ i, q i ∉ Set.range d.leftIn) ∧
      (∃ i, q i ∉ Set.range d.rightIn) := by
  obtain ⟨d⟩ :=
    hp.relationInputHull_reducible_of_reflectionFailure
      R xs hTarget hSource
  exact ⟨d, d.crossedInputGenerators C xs⟩

/-- A target-defined but source-undefined function tuple has
an equally concrete source-crossing certificate. It is NOT
an extra target value on an already source-defined fibre. -/
theorem IsEHNHomomorphismEmbedding.domainFailure_crossesSourceGenerators
    {C : Structure L U} {D : Structure L V} {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
    (hTarget : (D.func F (p ∘ xs)).Nonempty)
    (hSource : ¬ (C.func F xs).Nonempty) :
    let H := C.functionClosure (Set.range xs)
    let q : Fin (L.funcArity F) → H := fun i =>
      ⟨xs i, C.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
    ∃ d : ProperFreeDecomposition
        (C.induce H (C.functionClosure_isClosed (Set.range xs))),
      (∃ i, q i ∉ Set.range d.leftIn) ∧
      (∃ i, q i ∉ Set.range d.rightIn) := by
  obtain ⟨d⟩ :=
    hp.inputHull_reducible_of_domainFailure F xs hTarget hSource
  exact ⟨d, d.crossedInputGenerators C xs⟩

end StructuralRamsey.Structure
