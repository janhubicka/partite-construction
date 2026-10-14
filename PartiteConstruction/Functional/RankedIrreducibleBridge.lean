import PartiteConstruction.Functional.RankedPartialProjection

/-!
# Irreducible and closed supports survive singleton-rank reduction

The rank reduct forgets the names of singleton-valued partial
function ranks but retains their union as one set-valued function.
Since the union and each rank have exactly the same possible support,
a subset is closed in the ranked structure iff it is closed after
forgetting ranks.

Every free-amalgam diagram in the ranked language descends to a
free-amalgam diagram of the reduct. Consequently an irreducible
rank reduct has an irreducible ranked structure. This is the essential
first direction for lifting EHN protected tests after rank reduction.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U : Type v}

/-- A function-closed subset remains closed after taking the union
of all singleton-ranked function fibres. -/
theorem IsClosed.rankReduct
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U} {S : Set U}
    (hS : A.IsClosed S) :
    (Structure.rankReduct A).IsClosed S := by
  intro F x hx y hy
  change ∃ i : Fin n, y ∈ A.func (F, i) x at hy
  obtain ⟨i, hi⟩ := hy
  exact hS (F, i) x hx hi

/-- Conversely, union-closedness enforces closedness of each
individual ranked output fibre. -/
theorem IsClosed.of_rankReduct
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U} {S : Set U}
    (hS : (Structure.rankReduct A).IsClosed S) :
    A.IsClosed S := by
  intro Fi x hx y hy
  exact hS Fi.1 x hx ⟨Fi.2, hy⟩

/-- An irreducible union-of-ranks structure has an irreducible
ranked expansion. Any forbidden proper free decomposition of the
ranked structure would remain a free decomposition after
forgetting rank labels. -/
theorem Irreducible.of_rankReduct
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U}
    (hA : (Structure.rankReduct A).Irreducible) :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  exact hA hFree.rankReduct e.rankReduct

end StructuralRamsey.Structure
