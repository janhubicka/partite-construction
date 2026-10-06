import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Functional.WeakOperations

/-! # Descending pure-core domain failures

A functional Hales--Jewett core is a coordinate power of the weak restriction
of the previous Picture stage.  Fibre exactness shows that a domain-reflection
failure in the power occurs in one coordinate.  The weak restriction is taken
on a function-closed support, so fibre emptiness is unchanged when that
coordinate is viewed back in the previous stage.

Moreover the target domain remains present after applying the selected
embedding A -> D.  Hence every bad core domain descends to a genuine bad
domain of the previous EHN projection.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P U V : Type v}

namespace Induced

theorem power_weakRestrict_domainFailure_ambient
    (B : System L P V)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U)
    (α : Structure.Embedding A D)
    (N : ℕ)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) →
      Vertex (B.weakRestrict D hB.1 A α) N)
    (htgt :
      (A.func F
        ((power (B.weakRestrict D hB.1 A α) N).part ∘ x)).Nonempty)
    (hpow :
      ¬ ((power (B.weakRestrict D hB.1 A α) N).toStructure.func F x).Nonempty) :
    ∃ i : Fin N,
      (D.func F
        (B.part ∘
          (fun j => ((x j).coord i).1))).Nonempty ∧
      ¬ (B.toStructure.func F
        (fun j => ((x j).coord i).1)).Nonempty := by
  classical
  let R := B.weakRestrict D hB.1 A α
  have hR : R.WeaklyPartiteOver A :=
    B.weakRestrict_invariant D hB.1 A α hB
  obtain ⟨i, hi⟩ :=
    power_domainFailure_coordinate
      (A := A) (B := R) hR F x htgt hpow
  have hiAmbient :
      ¬ (B.toStructure.func F
        (fun j => ((x j).coord i).1)).Nonempty := by
    intro hamb
    have hres :
        (R.toStructure.func F
          (fun j => (x j).coord i)).Nonempty :=
      (B.weakRestrict_func_nonempty_iff D hB.1 A α F
        (fun j => (x j).coord i)).2 hamb
    exact hi hres
  obtain ⟨a, ha⟩ := htgt
  have haA :
      a ∈ A.func F
        (R.part ∘ (fun j => (x j).coord i)) := by
    have hargs :
        R.part ∘ (fun j => (x j).coord i) =
          (power R N).part ∘ x := by
      funext j
      exact (x j).belongs i
    rw [hargs]
    exact ha
  have haImg :
      α a ∈ imageSet α
        (A.func F
          (R.part ∘ (fun j => (x j).coord i))) :=
    ⟨a, haA, rfl⟩
  have haD0 :
      α a ∈ D.func F
        (α ∘
          (R.part ∘ (fun j => (x j).coord i))) := by
    rw [← α.map_func F
      (R.part ∘ (fun j => (x j).coord i))]
    exact haImg
  have hargsD :
      α ∘ (R.part ∘ (fun j => (x j).coord i)) =
        B.part ∘ (fun j => ((x j).coord i).1) := by
    funext j
    exact
      B.restrictedPart_spec α.toFunctionEmbedding
        ((x j).coord i)
  have haD :
      α a ∈ D.func F
        (B.part ∘ (fun j => ((x j).coord i).1)) := by
    rw [← hargsD]
    exact haD0
  exact ⟨i, ⟨α a, haD⟩, hiAmbient⟩


/-- If the ambient previous-stage EHN projection reflects function domains,
then the weak-restriction Hales--Jewett power reflects domains as well.  This
is the direct contrapositive of the domain-failure descent theorem above. -/
theorem power_weakRestrict_domainReflection
    (B : System L P V)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U)
    (α : Structure.Embedding A D)
    (N : ℕ)
    (hreflect :
      ∀ F (x : Fin (L.funcArity F) → V),
        (D.func F (B.part ∘ x)).Nonempty →
          (B.toStructure.func F x).Nonempty) :
    ∀ F (x : Fin (L.funcArity F) →
        Vertex (B.weakRestrict D hB.1 A α) N),
      (A.func F
        ((power (B.weakRestrict D hB.1 A α) N).part ∘ x)).Nonempty →
      ((power (B.weakRestrict D hB.1 A α) N).toStructure.func F x).Nonempty := by
  intro F x htgt
  by_contra hpow
  obtain ⟨i, htarget, hsource⟩ :=
    power_weakRestrict_domainFailure_ambient
      B D hB A α N F x htgt hpow
  exact hsource (hreflect F
    (fun j => ((x j).coord i).1) htarget)
end Induced
end StructuralRamsey.FunctionalPartite
