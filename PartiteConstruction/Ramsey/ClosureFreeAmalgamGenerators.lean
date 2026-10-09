import PartiteConstruction.Ramsey.ClosureProjectedRankGlue

/-! # Generators of a free source amalgam, including the boundary cost

If G generates the whole free amalgam, the generators on one side PLUS
its common root generate that side. It is in general incorrect simply
to intersect G with the side and discard the boundary contribution.

The projection consequence is more useful than a source-cardinality bound:
if a target-closed support contains the projected boundary and the images
of the generators on one side, it contains the image of that ENTIRE side.
This is proved from free-amalgam tuples, not assumed as a projection oracle.
No injectivity of the projection or closedness of its raw image is needed.

The final theorem combines this actual source geometry with rank budgets
and the closed-test mixed completion. Choosing a Picture cut whose two
supports meet those budgets remains a separate construction obligation.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {H E F C V : Type v}
variable {Root : RelStructure L H}
variable {Left : RelStructure L E} {Right : RelStructure L F}
variable {Whole : RelStructure L C}
variable {sL : Embedding Root Left} {sR : Embedding Root Right}
variable {iL : Embedding Left Whole} {iR : Embedding Right Whole}

/-- Side generators together with the full common root generate the
left side. This needs only the free relational tuple decomposition. -/
theorem IsFreeAmalgam.left_generated_over_root
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L) (G : Set C)
    (hGen : IsUGenerating rules Whole G) :
    IsUGenerating rules Left ((iL ⁻¹' G) ∪ Set.range sL) := by
  change UClosureHull rules Left ((iL ⁻¹' G) ∪ Set.range sL) = Set.univ
  apply Set.eq_univ_of_forall
  intro x T hT hGenerators
  have hCommon (r : H) : sL r ∈ T :=
    hGenerators (Or.inr ⟨r, rfl⟩)
  let TW : Set C := Set.range iR ∪ iL '' T
  have hTW : IsUSubstructure rules Whole TW := by
    intro rule hrule t ht hRoot j
    rcases (hFree.rel_iff rule.symbol t).mp ht with
        ⟨xs, hxs, heq⟩ | ⟨ys, hys, heq⟩
    · have hInput : ∀ k : Fin rule.rootSize,
          xs (k.castLE rule.rootLE) ∈ T := by
        intro k
        have hk : iL (xs (k.castLE rule.rootLE)) ∈ TW := by
          rw [← congrFun heq (k.castLE rule.rootLE)]
          exact hRoot k
        rcases hk with hR | hL
        · obtain ⟨r, hr⟩ := hR
          obtain ⟨d, hd, _⟩ :=
            (hFree.overlap (xs (k.castLE rule.rootLE)) r).mp hr.symm
          rw [hd]
          exact hCommon d
        · obtain ⟨a, ha, hae⟩ := hL
          have he : a = xs (k.castLE rule.rootLE) := iL.injective hae
          rw [← he]
          exact ha
      exact Or.inr ⟨xs j, hT rule hrule xs hxs hInput j,
        (congrFun heq j).symm⟩
    · exact Or.inl ⟨ys j, (congrFun heq j).symm⟩
  have hGTW : G ⊆ TW := by
    intro g hg
    rcases hFree.covers g with ⟨a, ha⟩ | ⟨b, hb⟩
    · have haG : a ∈ iL ⁻¹' G := by
        change iL a ∈ G
        rw [← ha]
        exact hg
      exact Or.inr ⟨a, hGenerators (Or.inl haG), ha.symm⟩
    · exact Or.inl ⟨b, hb.symm⟩
  have hxGen : iL x ∈ UClosureHull rules Whole G := by
    rw [hGen]
    trivial
  have hxTW : iL x ∈ TW := hxGen TW hTW hGTW
  rcases hxTW with hR | hL
  · obtain ⟨r, hr⟩ := hR
    obtain ⟨d, hd, _⟩ := (hFree.overlap x r).mp hr.symm
    rw [hd]
    exact hCommon d
  · obtain ⟨a, ha, hae⟩ := hL
    have he : a = x := iL.injective hae
    rw [← he]
    exact ha

/-- The symmetric generator statement. -/
theorem IsFreeAmalgam.right_generated_over_root
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L) (G : Set C)
    (hGen : IsUGenerating rules Whole G) :
    IsUGenerating rules Right ((iR ⁻¹' G) ∪ Set.range sR) :=
  hFree.swap.left_generated_over_root rules G hGen

/-- The whole left image lies in a target hull once that hull contains
the projected boundary and the projected generators on the left.
Only positivity of the global map is used in this geometric lemma. -/
theorem IsFreeAmalgam.left_projection_mem_hull
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L) (G : Set C)
    (hGen : IsUGenerating rules Whole G)
    {D : RelStructure L V} (p : C → V)
    (hp : Whole.IsHomomorphism D p)
    (J : Set V)
    (hBoundary : ∀ r, p (iL (sL r)) ∈ UClosureHull rules D J)
    (hGenerators : ∀ x : E, iL x ∈ G → p (iL x) ∈ UClosureHull rules D J) :
    ∀ x : E, p (iL x) ∈ UClosureHull rules D J := by
  have hpL : Left.IsHomomorphism D (p ∘ iL) := by
    intro R t ht
    exact hp R (iL ∘ t) ((iL.map_rel_iff R t).mpr ht)
  have hTarget := UClosureHull_isUSubstructure rules D J
  have hPre := hTarget.preimage_homomorphism hpL
  have hSupport : ((iL ⁻¹' G) ∪ Set.range sL) ⊆
      (p ∘ iL) ⁻¹' UClosureHull rules D J := by
    intro x hx
    rcases hx with hx | ⟨r, rfl⟩
    · exact hGenerators x hx
    · exact hBoundary r
  have hHull := UClosureHull_minimal rules Left hPre hSupport
  have hLeftGen := hFree.left_generated_over_root rules G hGen
  intro x
  apply hHull
  rw [hLeftGen]
  trivial

/-- Symmetric projected support containment. -/
theorem IsFreeAmalgam.right_projection_mem_hull
    (hFree : IsFreeAmalgam sL sR iL iR)
    (rules : ClosureDescription L) (G : Set C)
    (hGen : IsUGenerating rules Whole G)
    {D : RelStructure L V} (p : C → V)
    (hp : Whole.IsHomomorphism D p)
    (J : Set V)
    (hBoundary : ∀ r, p (iR (sR r)) ∈ UClosureHull rules D J)
    (hGenerators : ∀ x : F, iR x ∈ G → p (iR x) ∈ UClosureHull rules D J) :
    ∀ x : F, p (iR x) ∈ UClosureHull rules D J :=
  hFree.swap.left_projection_mem_hull rules G hGen p hp J hBoundary hGenerators

/-- A concrete free-amalgam support criterion using the generators of
the WHOLE source. All side-image containments and shared boundary data
are derived; the two small supports must still contain the projected
boundary and the corresponding projected generators. -/
theorem HasClosedUKCompletion.of_whole_generated_projection_supports
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hK : HasFiniteStrongAmalgamation K)
    (hHereditary : ∀ {X Y : Type v}
      {E : RelStructure L X} {F : RelStructure L Y},
      K F → IsUClosed rules E → Embedding E F → K E)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    {UA : Type v} {A : RelStructure L UA} {D : RelStructure L V}
    [Finite V] [DecidableEq V]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left) (hRight : IsUSemiClosed rules Right)
    (hKA : K A) (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D) (p : C → V)
    (hp : IsClosedUHomomorphismEmbedding rules Whole D p)
    (hSeparator : ∀ r : H, p (iL (sL r)) ∈ Set.range a)
    (G : Set C) (hGen : IsUGenerating rules Whole G)
    (JL JR : Finset V) (j : ℕ)
    (hJL : JL.card ≤ j) (hJR : JR.card ≤ j)
    (hBoundaryL : ∀ r, p (iL (sL r)) ∈ UClosureHull rules D (↑JL : Set V))
    (hBoundaryR : ∀ r, p (iR (sR r)) ∈ UClosureHull rules D (↑JR : Set V))
    (hGL : ∀ x : E, iL x ∈ G → p (iL x) ∈ UClosureHull rules D (↑JL : Set V))
    (hGR : ∀ x : F, iR x ∈ G → p (iR x) ∈ UClosureHull rules D (↑JR : Set V))
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T)) :
    HasClosedUKCompletion K rules Whole := by
  have hRangeL := hSrc.left_projection_mem_hull rules G hGen
    p hp.1 (↑JL : Set V) hBoundaryL hGL
  have hRangeR := hSrc.right_projection_mem_hull rules G hGen
    p hp.1 (↑JR : Set V) hBoundaryR hGR
  exact HasClosedUKCompletion.of_common_projection_supports
    rules hK hHereditary hKIrr hSrc hRoot hLeft hRight hKA hA hD
    a p hp hSeparator JL JR j hJL hJR hRangeL hRangeR hRank

end StructuralRamsey.RelStructure
