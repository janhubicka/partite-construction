import PartiteConstruction.Functional.FreeAmalgamGeneratorBudget

/-!
# Precise exterior-generator budget in a full functional free amalgam

The checked budget previously added the cardinality of the whole common
root. This generalization uses a specified GENERATING SET of the root
and a disjoint reserve of OUTSIDE generators of the whole source.

If R generates the common root, G generates the whole structure, and
Out ⊆ G lies outside the left embedded side, then
  rank(Left) <= |G| - |Out| + |R|.
In particular if |R| ≤ |Out|, the closed left side has the SAME
generator rank budget as the original whole structure.

This is a theorem about arbitrary genuine full set-valued-function
free amalgams; it does not require root irreducibility and does not
assume that a maximal EHN mixed test automatically has enough outside
generators. This quantifies exactly where generator-rank inflation
can enter the published functional Picture induction.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam
universe u v
variable {L : Language.{u}}
variable {H E F C : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}

/-- An explicitly chosen exterior generator reserve pays for
the function closure of a finite generating set of the common
root when generating the closed LEFT side. -/
theorem left_generatedByAtMost_of_exterior_root_seeds
    [Finite H] [Finite E]
    (hfree : IsFreeAmalgam sL sR iL iR)
    (G : Finset C)
    (hGgen : Whole.GeneratedBy (↑G : Set C))
    (Roots : Finset H)
    (hRootGen : Root.GeneratedBy (↑Roots : Set H))
    (Out : Finset C)
    (hOutSubset : Out ⊆ G)
    (hOutOutside : ∀ g ∈ Out, g ∉ Set.range iL)
    (hOutPaysRoot : Roots.card ≤ Out.card)
    {n : ℕ}
    (hGcard : G.card ≤ n) :
    Left.GeneratedByAtMost n := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype E := Fintype.ofFinite E

  let leftGen : Finset E :=
    (Finset.univ : Finset E).filter (fun x => iL x ∈ G)
  let rootGen : Finset E :=
    Roots.image sL
  let generators : Finset E := leftGen ∪ rootGen

  have hLeftGenCard : leftGen.card ≤ (G \ Out).card := by
    let phi : ↥(↑leftGen : Set E) → ↥(↑(G \ Out) : Set C) :=
      fun x => ⟨iL x.1, by
        apply Finset.mem_sdiff.mpr
        constructor
        · exact (Finset.mem_filter.mp x.2).2
        · intro hx
          exact (hOutOutside (iL x.1) hx) ⟨x.1, rfl⟩⟩
    have hphi : Function.Injective phi := by
      intro x y hxy
      apply Subtype.ext
      apply iL.injective
      exact congrArg Subtype.val hxy
    calc
      leftGen.card = Fintype.card ↥(↑leftGen : Set E) := by simp
      _ ≤ Fintype.card ↥(↑(G \ Out) : Set C) :=
        Fintype.card_le_of_injective phi hphi
      _ = (G \ Out).card := Fintype.card_coe (G \ Out)

  have hRootGenCard : rootGen.card ≤ Roots.card :=
    Finset.card_image_le
  have hCardBound : leftGen.card + rootGen.card ≤ G.card := by
    have hSplit : (G \ Out).card + Out.card = G.card :=
      Finset.card_sdiff_add_card_eq_card hOutSubset
    omega

  refine ⟨generators, ?_, ?_⟩
  · calc
      generators.card ≤ leftGen.card + rootGen.card :=
        Finset.card_union_le _ _
      _ ≤ G.card := hCardBound
      _ ≤ n := hGcard
  · ext x
    constructor
    · intro _
      simp
    · intro _
      intro T hT hGeneratorsT

      let TWhole : Set C :=
        Set.range iR ∪ iL '' T

      have hCommonT : ∀ d : H, sL d ∈ T := by
        have hPre : Root.IsClosed {d : H | sL d ∈ T} :=
          sL.preimage_isClosed T hT
        have hSeeds : (↑Roots : Set H) ⊆ {d : H | sL d ∈ T} := by
          intro d hd
          apply hGeneratorsT
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
        intro d
        have hd : d ∈ Root.functionClosure (↑Roots : Set H) := by
          rw [hRootGen]
          exact Set.mem_univ d
        exact hd {d : H | sL d ∈ T} hPre hSeeds

      have hTWholeClosed : Whole.IsClosed TWhole := by
        intro F0 args hargs y hy
        rcases (hfree.func_iff F0 args y).mp hy with
          hleft | hright
        · rcases hleft with ⟨a, b, hb, hargsEq, hyEq⟩
          have haT : ∀ k, a k ∈ T := by
            intro k
            have hk : iL (a k) ∈ TWhole := by
              have hk0 := hargs k
              rw [hargsEq] at hk0
              exact hk0
            rcases hk with hR | hL
            · rcases hR with ⟨r, hr⟩
              obtain ⟨d, had, _⟩ :=
                (hfree.overlap (a k) r).mp hr.symm
              rw [had]
              exact hCommonT d
            · rcases hL with ⟨a', ha'T, ha'eq⟩
              have haa : a' = a k := iL.injective ha'eq
              simpa [haa] using ha'T
          have hbT : b ∈ T := hT F0 a haT hb
          exact Or.inr ⟨b, hbT, hyEq.symm⟩
        · rcases hright with ⟨a, b, hb, hargsEq, hyEq⟩
          exact Or.inl ⟨b, hyEq.symm⟩

      have hGTWhole : (↑G : Set C) ⊆ TWhole := by
        intro g hg
        rcases hfree.covers g with ⟨l, hgl⟩ | ⟨r, hgr⟩
        · have hlLeftGen : l ∈ leftGen := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ l, by simpa [hgl] using hg⟩
          have hlT : l ∈ T := by
            apply hGeneratorsT
            exact Finset.mem_union_left rootGen hlLeftGen
          exact Or.inr ⟨l, hlT, hgl.symm⟩
        · exact Or.inl ⟨r, hgr.symm⟩

      have hxWhole : iL x ∈ TWhole := by
        have hxClosure : iL x ∈ Whole.functionClosure (↑G : Set C) := by
          rw [hGgen]
          simp
        exact hxClosure TWhole hTWholeClosed hGTWhole

      rcases hxWhole with hR | hL
      · rcases hR with ⟨r, hr⟩
        obtain ⟨d, hxd, _⟩ :=
          (hfree.overlap x r).mp hr.symm
        rw [hxd]
        exact hCommonT d
      · rcases hL with ⟨l, hlT, hleq⟩
        have hlx : l = x := iL.injective hleq
        simpa [hlx] using hlT


end StructuralRamsey.Structure.IsFreeAmalgam
