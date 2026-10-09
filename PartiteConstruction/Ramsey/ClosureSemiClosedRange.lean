import PartiteConstruction.Ramsey.ClosureSemiClosed2019

/-! # Exact U-substructure images in semi-closed targets

The range theorem for full embeddings of U-closed structures does not
require the ambient target to be U-closed. U-semi-closedness suffices:
the source provides a closure tuple above an embedded root, while
partial uniqueness in the target forces every existing tuple with
that root to coincide with the source tuple.

This is useful in the intermediate 2019 Picture constructions:
the target can have undefined closure roots, but a copy of a
fully U-closed source cannot acquire new outputs above its roots.

Everything is on the exact set-theoretic range, with no completion
or closure hull of the projected image.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- The image of a full embedding of a U-closed structure into a
U-**semi**-closed target is a vertex-exact U-substructure.

The target is *not* required to contain a closure tuple above
every embedded root. The source already supplies one on each
of its roots; uniqueness is the only target hypothesis needed. -/
theorem Embedding.range_isUSubstructure_of_semiClosed
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (hA : IsUClosed rules A)
    (hB : IsUSemiClosed rules B)
    (e : Embedding A B) :
    IsUSubstructure rules B (Set.range e) := by
  classical
  intro rule hrule t ht hRootRange j
  obtain ⟨rootB, hRootB⟩ := (hB rule hrule).1 t ht
  have hrange : ∀ i : Fin rule.rootSize,
      ∃ a : U, rootB i = e a := by
    intro i
    obtain ⟨a, ha⟩ := hRootRange i
    exact ⟨a, (hRootB i).symm.trans ha.symm⟩
  let rootA : Embedding rule.root A :=
    rootB.factorThroughRangeHeterogeneous e hrange
  have hRootA (i : Fin rule.rootSize) :
      rootB i = e (rootA i) :=
    Classical.choose_spec (hrange i)
  obtain ⟨tA, htA, _⟩ := (hA rule hrule).2 rootA
  have htB : B.rel rule.symbol (e ∘ tA) :=
    (e.map_rel_iff rule.symbol tA).mpr htA.1
  have hRootImage :
      ∀ i : Fin rule.rootSize,
        (e ∘ tA) (i.castLE rule.rootLE) = rootB i := by
    intro i
    change e (tA (i.castLE rule.rootLE)) = rootB i
    rw [htA.2 i]
    exact (hRootA i).symm
  have hRootEq :
      ∀ i : Fin rule.rootSize,
        t (i.castLE rule.rootLE) =
          (e ∘ tA) (i.castLE rule.rootLE) := by
    intro i
    exact (hRootB i).trans (hRootImage i).symm
  have heq : t = e ∘ tA :=
    (hB rule hrule).2 t (e ∘ tA) ht htB hRootEq
  rw [heq]
  exact ⟨tA j, rfl⟩

end StructuralRamsey.RelStructure
