import PartiteConstruction.Functional.QuotientBoundaryDiary

/-! # Domain failures rule out a single full functional control copy

A proposed shortcut for the reducible separator in the functional Picture
step is to realize its possibly noninjective A-labelling inside one full
A-copy of a strict B-tree. This cannot work when the root label map
fails to reflect a function domain.

Indeed, the existing quotient-boundary cancellation lemma shows that
such a realization forces the label map to be a full homomorphism. A
nonempty target fibre over an empty source fibre gives a contradiction.

This is an obstruction to the *single-control-copy* root strategy, not a
counterexample to the possibility of a common root which is itself a
strict tree of B-copies. -/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U W Y : Type v}

/-- If a quotient-labelled separator has an empty function fibre over
some tuple but its prescribed A-labels have a defined function value,
there is no full functional completion which realizes that separator
inside one isolated full A-copy. -/
theorem IsolatedQuotientBoundary.false_of_domainFailure
    {A : Structure L U} {C : Structure L W}
    {r : QuotientBoundaryRequest A C}
    {T : Structure L Y} {f : W → Y}
    (hf : C.IsHomomorphismEmbedding T f)
    (hIso : IsolatedQuotientBoundary r T f)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → r.Carrier)
    (hSource : ¬ (r.source.func F x).Nonempty)
    (hTarget : (A.func F (r.label ∘ x)).Nonempty) :
    False := by
  have hLabel : r.source.IsHomomorphism A r.label :=
    hIso.label_isHomomorphism hf.1
  obtain ⟨y, hy⟩ := hTarget
  have hImage : y ∈ imageSet r.label (r.source.func F x) := by
    rw [hLabel.2 F x]
    exact hy
  obtain ⟨z, hz, _⟩ := hImage
  exact hSource ⟨z, hz⟩

end StructuralRamsey.Structure
