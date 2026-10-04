import PartiteConstruction.Structure.Relationalize

/-! # Collapsing input fibres does not give a full homomorphism

The two-point structure has a unary partial function F(false) = {false}
and F(true) = empty. Its source-generated incidence image under the collapse
to one point has F(*) = {*}. Thus the collapse preserves every graph tuple,
but it does not map each source function fibre onto its target fibre.

This regression test is independent of the active EHN construction. It
prevents confusing a weak graph homomorphism with the survey's stronger
set-valued-function homomorphism at a noninjective quotient.
-/
namespace StructuralRamsey.Structure.QuotientFibreObstruction

def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 1

def source : Structure language Bool where
  rel R := Empty.elim R
  func _ x := {y | x 0 = false ∧ y = false}

def target : Structure language Unit where
  rel R := Empty.elim R
  func _ _ := Set.univ

def collapse : Bool → Unit := fun _ => ()

theorem collapse_surjective : Function.Surjective collapse := by
  intro y
  exact ⟨false, Subsingleton.elim _ _⟩

/-- The target is exactly the incidence-generated image, not an arbitrary
larger target with gratuitously added function values. -/
theorem generated_image_exact (x : Fin 1 → Unit) (y : Unit) :
    y ∈ target.func () x ↔
      ∃ a : Fin 1 → Bool, ∃ b : Bool,
        b ∈ source.func () a ∧ collapse ∘ a = x ∧ collapse b = y := by
  constructor
  · intro _
    exact ⟨fun _ => false, false, ⟨rfl, rfl⟩,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · intro _
    exact Set.mem_univ y

/-- The collapse preserves all relational graph incidences. -/
theorem collapse_graph_hom :
    source.graph.IsHomomorphism target.graph collapse := by
  intro R x hx
  cases R with
  | inl R => exact Empty.elim R
  | inr F => exact Set.mem_univ _

/-- The same collapse is not a full set-valued-function homomorphism. -/
theorem collapse_not_full_hom :
    ¬ source.IsHomomorphism target collapse := by
  intro h
  have hf := h.2 () (fun _ => true)
  have hy : () ∈ target.func () (collapse ∘ (fun _ => true)) :=
    Set.mem_univ ()
  have hmem : () ∈ imageSet collapse (source.func () (fun _ => true)) := by
    rw [hf]
    exact hy
  obtain ⟨b, hb, _⟩ := hmem
  change true = false ∧ b = false at hb
  cases hb.1

end StructuralRamsey.Structure.QuotientFibreObstruction
