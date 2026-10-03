import PartiteConstruction.Iterated.FreeAmalgam

/-! # Indexed target copies over a fixed irreducible support

A finite family of copies of `Base` can be attached successively to a tree
amalgam along prescribed embeddings of one fixed irreducible support
`Base.induce S`.  The resulting tree amalgam retains the original target and
an individually addressable copy of `Base` for every index.

This is a target-side bookkeeping lemma for the uniform final-attachment
argument.  No bound is placed on the target size.
-/
namespace StructuralRamsey.RelStructure.TreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {VB Y I : Type v}
variable {Base : RelStructure L VB} {T₀ : RelStructure L Y}
variable {S : Set VB}

/-- Every tree amalgam contains an embedded copy of its base. -/
theorem exists_base_embedding
    (hT : TreeAmalgam Base Y T₀) :
    Nonempty (Embedding Base T₀) := by
  induction hT with
  | copy h =>
      exact ⟨h.toEmbedding⟩
  | @glue W₁ W₂ Z W T₁ T₂ D T h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      rcases ih₁ with ⟨e⟩
      exact ⟨i₁.comp e⟩

/-- Attach target copies indexed by a finite list.  The `copies` function is
defined for every index; the extension identity is promised on members of the
processed list. -/
theorem attachIndexedList
    [DecidableEq I]
    (hRoot : (Base.induce S).Irreducible)
    (hTree : TreeAmalgam Base Y T₀)
    (t : I → Embedding (Base.induce S) T₀)
    (xs : List I) :
    ∃ (Z : Type v) (T : RelStructure L Z),
      TreeAmalgam Base Z T ∧
      ∃ core : Embedding T₀ T,
        ∃ copies : I → Embedding Base T,
          ∀ i, i ∈ xs →
            ∀ x : ↥S, copies i x.1 = core (t i x) := by
  classical
  induction xs with
  | nil =>
      rcases hTree.exists_base_embedding with ⟨eBase⟩
      refine ⟨Y, T₀, hTree, Embedding.id T₀, (fun _ => eBase), ?_⟩
      intro i hi
      simp at hi
  | cons i xs ih =>
      obtain ⟨Z, T, hTreeT, core, copies, hcopies⟩ := ih
      let rootT : Embedding (Base.induce S) T := core.comp (t i)
      let rootB : Embedding (Base.induce S) Base :=
        inclusion Base S
      let Whole := FreeAmalgam.amalgam (Base.induce S) T Base rootT rootB
      let l : Embedding T Whole :=
        FreeAmalgam.leftEmbedding (Base.induce S) T Base rootT rootB
      let r : Embedding Base Whole :=
        FreeAmalgam.rightEmbedding (Base.induce S) T Base rootT rootB
      have hcT : rootT.ContainedInIrreducible := by
        exact ⟨Set.range rootT, hRoot.range_embedding rootT,
          fun x => ⟨x, rfl⟩⟩
      have hcB : rootB.ContainedInIrreducible := by
        exact ⟨Set.range rootB, hRoot.range_embedding rootB,
          fun x => ⟨x, rfl⟩⟩
      have hTreeWhole :
          TreeAmalgam Base
            (FreeAmalgam.Vertex (Base.induce S) T Base rootT rootB) Whole :=
        FreeAmalgam.treeAmalgam
          (Base.induce S) T Base rootT rootB Base
          hTreeT (TreeAmalgam.copy (Iso.refl Base)) hcT hcB
      let core' : Embedding T₀ Whole := l.comp core
      let copies' : I → Embedding Base Whole := fun j =>
        if hji : j = i then
          r
        else
          l.comp (copies j)
      refine ⟨_, Whole, hTreeWhole, core', copies', ?_⟩
      intro j hj x
      rcases List.mem_cons.mp hj with hji | hj
      · subst j
        simp only [copies', dif_pos rfl]
        change
          r x.1 = l (core (t i x))
        have hov :=
          FreeAmalgam.left_right_overlap
            (Base.induce S) T Base rootT rootB x
        change l (rootT x) = r (rootB x) at hov
        exact hov.symm
      · by_cases hji : j = i
        · subst j
          simp only [copies', dif_pos rfl]
          change r x.1 = l (core (t i x))
          have hov :=
            FreeAmalgam.left_right_overlap
              (Base.induce S) T Base rootT rootB x
          change l (rootT x) = r (rootB x) at hov
          exact hov.symm
        · simp only [copies', dif_neg hji]
          change l (copies j x.1) = l (core (t j x))
          exact congrArg l (hcopies j hj x)

/-- Finite indexed version of `attachIndexedList`. -/
theorem attachIndexed
    [Fintype I]
    (hRoot : (Base.induce S).Irreducible)
    (hTree : TreeAmalgam Base Y T₀)
    (t : I → Embedding (Base.induce S) T₀) :
    ∃ (Z : Type v) (T : RelStructure L Z),
      TreeAmalgam Base Z T ∧
      ∃ core : Embedding T₀ T,
        ∃ copies : I → Embedding Base T,
          ∀ i x, copies i x.1 = core (t i x) := by
  classical
  obtain ⟨Z, T, hT, core, copies, hcopies⟩ :=
    attachIndexedList hRoot hTree t (Finset.univ.toList)
  refine ⟨Z, T, hT, core, copies, ?_⟩
  intro i x
  exact hcopies i (by simp) x

end StructuralRamsey.RelStructure.TreeAmalgam
