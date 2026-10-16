import PartiteConstruction.Functional.SetAmbientRelativeTreeHistory
import PartiteConstruction.Functional.ProjectedHistoryFactor

/-!
# Root-projection factorization from singleton histories of exact weak tests

The strict functional partite Picture induction keeps FINITE projected
history diaries on the EXACT weak tested vertex set S. If the history
includes every singleton subset of the finite outer part carrier P,
then a target identification cannot equate source vertices in different
projected parts.

For a chosen map q of an arbitrary weak source root into a common
strict functional Start tree, suppose the side witness sends each
weak-root vertex to the image of q under a FULL embedding of Start
into the side's strict target. Then the projected labels on the weak
root factor through q, even if q is NONINJECTIVE.

This is the correct automatic root-factor lemma. It must NOT be
confused with a stronger and generally false statement that EVERY
side vertex whose image happens to land inside the target Start must
have its label determined by q. For the latter, the maximal mixed
construction must supply an additional root-hitting/label safety
certificate, or prove such safety from its genuine Hales-Jewett
history. The new code does not assume arbitrary root isolation.

No function closure hull or singleton-valued operations are involved.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {W Y H G P : Type v}

/-- Projected singleton histories force the projection of a chosen
weak root to factor through the root map into a strict functional
tree Start. This holds for an arbitrary weak tested subset, a
possibly noninjective q, and any full embedding of Start into
the witness target. -/
theorem SetRespectsProjectedHistory.factors_through_weakRoot
    [Nonempty P]
    {Target : Structure L Y}
    {Start : Structure L G}
    {S : Set W} {p : W → P} {f : S → Y}
    {history : List (Set P)}
    (hHistory : SetRespectsProjectedHistory p S f history)
    (hSingletons : ∀ a : P, Set.singleton a ∈ history)
    (root : H → S) (q : H → G)
    (j : Embedding Start Target)
    (hRoot : ∀ a : H, f (root a) = j (q a)) :
    ∃ pG : G → P,
      ∀ a : H, p (root a).1 = pG (q a) := by
  have hRootHistory :
      ∀ K ∈ history, ∀ a b : H,
        q a = q b →
        (p (root a).1 ∈ K ↔ p (root b).1 ∈ K) := by
    intro K hK a b hab
    apply hHistory K hK (root a) (root b)
    calc
      f (root a) = j (q a) := hRoot a
      _ = j (q b) := congrArg j hab
      _ = f (root b) := (hRoot b).symm
  exact projectedMap_factors_of_singletonHistory
    (fun a : H => p (root a).1) q
    history hSingletons hRootHistory

/-- In the actual finite partite induction it suffices to append the
standard finite singleton diary to whichever projected history the
caller wishes to preserve. The resulting pG is a witness to
root-projection factorization, NOT automatic root-hitting safety. -/
theorem SetRespectsProjectedHistory.factors_through_weakRoot_of_singletons
    [Fintype P] [Nonempty P]
    {Target : Structure L Y}
    {Start : Structure L G}
    {S : Set W} {p : W → P} {f : S → Y}
    {history : List (Set P)}
    (hHistory : SetRespectsProjectedHistory p S f
      (history ++ singletonProjectedHistory P))
    (root : H → S) (q : H → G)
    (j : Embedding Start Target)
    (hRoot : ∀ a : H, f (root a) = j (q a)) :
    ∃ pG : G → P,
      ∀ a : H, p (root a).1 = pG (q a) := by
  apply hHistory.factors_through_weakRoot
    (fun a : P => List.mem_append.mpr
      (Or.inr (singleton_mem_singletonProjectedHistory a)))
    root q j hRoot

/-- Additional ROOT-HIT SAFETY makes the factor map valid on all
tested side vertices landing inside the distinguished target root.
This explicitly isolates the second, nonautomatic requirement of
the native maximal-mixed weak-root construction.

The containment assumption is only on actual *target root hits*:
if a side vertex lands in j[G], its source is a chosen weak-root
vertex with exactly the corresponding q label. It is NOT assumed
for every side vertex and is not inferred from arbitrary tree
completions. -/
theorem SetRespectsProjectedHistory.root_labels_safe_of_isolated_hits
    [Nonempty P]
    {Target : Structure L Y}
    {Start : Structure L G}
    {S : Set W} {p : W → P} {f : S → Y}
    {history : List (Set P)}
    (hHistory : SetRespectsProjectedHistory p S f history)
    (hSingletons : ∀ a : P, Set.singleton a ∈ history)
    (root : H → S) (q : H → G)
    (j : Embedding Start Target)
    (hRoot : ∀ a : H, f (root a) = j (q a))
    (hHits : ∀ (x : S) (g : G),
      f x = j g →
      ∃ a : H, root a = x ∧ q a = g) :
    ∃ pG : G → P,
      (∀ a : H, p (root a).1 = pG (q a)) ∧
      (∀ (x : S) (g : G), f x = j g →
        p x.1 = pG g) := by
  obtain ⟨pG, hFactor⟩ :=
    hHistory.factors_through_weakRoot hSingletons root q j hRoot
  refine ⟨pG, hFactor, ?_⟩
  intro x g hx
  obtain ⟨a, ha, hq⟩ := hHits x g hx
  calc
    p x.1 = p (root a).1 := by rw [ha]
    _ = pG (q a) := hFactor a
    _ = pG g := by rw [hq]

end StructuralRamsey.Structure
