import PartiteConstruction.Partite.Induced

/-! # Coordinate embeddings of irreducible copies in an induced power

An induced copy of an irreducible control structure inside a positive
coordinatewise power projects along every coordinate to an induced copy in
the base partite system.

Preservation is coordinatewise.  Reflection uses the partite projection:
the whole A-copy has an induced projection into A, so any relation appearing
at one coordinate maps to a relation of A on the same projected tuple.
-/
namespace StructuralRamsey.Partite.Induced

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {P V : Type v}
variable {A : RelStructure L P}
variable {B : Partite.System L P V}
variable {N : ℕ}

/-- Every coordinate of an irreducible A-copy in the power is an induced
embedding back into B. -/
theorem embedding_coordinate
    (hA : A.Irreducible)
    (hB : B.IsPartiteOver A)
    (hN : 0 < N)
    (e : RelStructure.Embedding A (power B N).toRelStructure)
    (k : Fin N) :
    ∃ c : RelStructure.Embedding A B.toRelStructure,
      ∀ a : P, c a = (e a).coord k := by
  classical
  obtain ⟨q, hq⟩ :=
    (power_isPartiteOver hB hN).after_irreducible_embedding hA e
  let coord : P → V := fun a => (e a).coord k
  have hcoordPart (a : P) :
      B.part (coord a) = q a := by
    calc
      B.part (coord a) = (power B N).part (e a) := (e a).belongs k
      _ = q a := (hq a).symm
  have hinj : Function.Injective coord := by
    intro a b hab
    apply q.injective
    rw [← hcoordPart a, ← hcoordPart b, hab]
  let c : RelStructure.Embedding A B.toRelStructure := {
    toFun := coord
    injective := hinj
    map_rel_iff := by
      intro R x
      constructor
      · intro hBrel
        have hArel : A.rel R (B.part ∘ (coord ∘ x)) :=
          hB.1 R (coord ∘ x) hBrel
        have heq : B.part ∘ (coord ∘ x) = q ∘ x := by
          funext i
          exact hcoordPart (x i)
        rw [heq] at hArel
        exact (q.map_rel_iff R x).mp hArel
      · intro hArel
        have hPow :
            (power B N).rel R (e ∘ x) :=
          (e.map_rel_iff R x).mpr hArel
        exact hPow k
  }
  exact ⟨c, fun _ => rfl⟩

end StructuralRamsey.Partite.Induced
