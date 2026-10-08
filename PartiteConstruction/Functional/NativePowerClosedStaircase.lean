import PartiteConstruction.Functional.NativePowerInputTree

/-! # A closed staircase test inside the actual native power

The six selected input vertices of the genuine tagged second power produce
exactly six function-output vertices. We retain those outputs explicitly,
rather than closing the projected weak image or taking the function hull
of an arbitrary tested set.

The induced structure on this chosen support is function-closed and already
has no strict full-functional tree completion. The explicit cardinality
certificate (twelve vertices) is a separate subsequent proof obligation;
the theorem here establishes closure and target obstruction first.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

abbrev PowerVertex := FunctionalPartite.Induced.Vertex oldSystem 2

/-- In the seven-vertex stage a defined binary fibre always has an
X-input, a Y-input and a Z-output. -/
theorem oldOutput_all_roles
    (a b c : Fin 7) (h : oldOutput a b = some c) :
    oldPart a = 0 ∧ oldPart b = 1 ∧ oldPart c = 2 := by
  have hc : ∀ (x y z : Fin 7),
      oldOutput x y = some z →
      oldPart x = 0 ∧ oldPart y = 1 ∧ oldPart z = 2 := by decide
  exact hc a b c h

theorem actualPower_output_roles
    (a b c : PowerVertex)
    (h : c ∈ actualPower.func () ![a,b]) :
    a.part = 0 ∧ b.part = 1 ∧ c.part = 2 := by
  have h0 :
      oldOutput (a.coord 0) (b.coord 0) = some (c.coord 0) := h 0
  obtain ⟨ha,hb,hc⟩ := oldOutput_all_roles _ _ _ h0
  exact ⟨(a.belongs 0).symm.trans ha,
    (b.belongs 0).symm.trans hb,
    (c.belongs 0).symm.trans hc⟩

/-- Six chosen inputs (three in each role), together with precisely
the function outputs of their defined pairs. No other vertices are added. -/
def StaircaseSupport : Set PowerVertex := {v |
    (∃ i : Fin 3, v = powerX i) ∨
    (∃ j : Fin 3, v = powerY j) ∨
    (∃ i j : Fin 3, v ∈ actualPower.func () ![powerX i,powerY j])}

theorem powerX_mem_support (i : Fin 3) :
    powerX i ∈ StaircaseSupport :=
  Or.inl ⟨i,rfl⟩

theorem powerY_mem_support (j : Fin 3) :
    powerY j ∈ StaircaseSupport :=
  Or.inr (Or.inl ⟨j,rfl⟩)

/-- The only X-vertices on this support are the three selected X-inputs. -/
theorem support_X_is_selected
    (v : PowerVertex) (hv : v ∈ StaircaseSupport)
    (hpart : v.part = 0) :
    ∃ i : Fin 3, v = powerX i := by
  rcases hv with hX | hY | hZ
  · exact hX
  · obtain ⟨j,hj⟩ := hY
    have hwrong : (1 : Fin 3) = 0 := by
      simpa only [hj, powerY] using hpart
    exact (by decide : (1 : Fin 3) ≠ 0) hwrong |>.elim
  · obtain ⟨i,j,hz⟩ := hZ
    have hwrong : (2 : Fin 3) = 0 := by
      exact ((actualPower_output_roles _ _ _ hz).2.2).symm.trans hpart
    exact (by decide : (2 : Fin 3) ≠ 0) hwrong |>.elim

/-- Similarly, the only Y-vertices on the support are the selected ones. -/
theorem support_Y_is_selected
    (v : PowerVertex) (hv : v ∈ StaircaseSupport)
    (hpart : v.part = 1) :
    ∃ j : Fin 3, v = powerY j := by
  rcases hv with hX | hY | hZ
  · obtain ⟨i,hi⟩ := hX
    have hwrong : (0 : Fin 3) = 1 := by
      simpa only [hi, powerX] using hpart
    exact (by decide : (0 : Fin 3) ≠ 1) hwrong |>.elim
  · exact hY
  · obtain ⟨i,j,hz⟩ := hZ
    have hwrong : (2 : Fin 3) = 1 := by
      exact ((actualPower_output_roles _ _ _ hz).2.2).symm.trans hpart
    exact (by decide : (2 : Fin 3) ≠ 1) hwrong |>.elim

/-- Every defined output of two supported inputs is one of the explicitly
included staircase outputs. The chosen support is function-closed. -/
theorem staircaseSupport_closed :
    actualPower.IsClosed StaircaseSupport := by
  intro F xs hxs z hz
  cases F
  have hargs : xs = ![xs (0 : Fin 2),xs (1 : Fin 2)] := by
    funext i
    fin_cases i <;> rfl
  have hval : z ∈ actualPower.func ()
      ![xs (0 : Fin 2),xs (1 : Fin 2)] := by
    rw [hargs] at hz
    exact hz
  have hroles :=
    actualPower_output_roles
      (xs (0 : Fin 2)) (xs (1 : Fin 2)) z hval
  obtain ⟨i,hi⟩ :=
    support_X_is_selected _ (hxs (0 : Fin 2)) hroles.1
  obtain ⟨j,hj⟩ :=
    support_Y_is_selected _ (hxs (1 : Fin 2)) hroles.2.1
  apply Or.inr
  apply Or.inr
  refine ⟨i,j,?_⟩
  rw [← hi, ← hj]
  exact hval

/-- The *closed induced substructure* of the native power already
obstructs every strict full-functional B-tree completion. -/
theorem staircaseSupport_no_strictTreeCompletion :
    ¬ HasTreeCompletion toyBase
      (actualPower.induce StaircaseSupport staircaseSupport_closed) := by
  rintro ⟨W,T,hTree,f,hf⟩
  let Small := actualPower.induce StaircaseSupport staircaseSupport_closed
  let sx (i : Fin 3) : StaircaseSupport :=
    ⟨powerX i,powerX_mem_support i⟩
  let sy (j : Fin 3) : StaircaseSupport :=
    ⟨powerY j,powerY_mem_support j⟩
  have hDomain (i j : Fin 3) :
      Domain T (f (sx i)) (f (sy j)) ↔ Staircase i j := by
    calc
      Domain T (f (sx i)) (f (sy j)) ↔
          Domain Small (sx i) (sy j) :=
        domain_fullHom_iff hf.1 (sx i) (sy j)
      _ ↔ Domain actualPower (powerX i) (powerY j) := by
        constructor
        · rintro ⟨z,hz⟩
          exact ⟨z.1,hz⟩
        · rintro ⟨z,hz⟩
          have hs : z ∈ StaircaseSupport :=
            Or.inr (Or.inr ⟨i,j,hz⟩)
          exact ⟨⟨z,hs⟩,hz⟩
      _ ↔ Staircase i j := actualPowerDomain_iff_staircase i j
  let XRole := {x : W // Role T 0 x}
  let YRole := {y : W // Role T 1 y}
  let R : XRole → YRole → Prop := fun x y => Domain T x.1 y.1
  have hNoSquare : NoSquare R := by
    intro x₁ x₂ y₁ y₂ hxx hyy h₁₁ h₁₂ h₂₁ h₂₂
    have hxx' : x₁.1 ≠ x₂.1 := by
      intro h
      exact hxx (Subtype.ext h)
    have hyy' : y₁.1 ≠ y₂.1 := by
      intro h
      exact hyy (Subtype.ext h)
    exact (strictTree_squareFree hTree)
      x₁.1 x₂.1 y₁.1 y₂.1
      x₁.2 x₂.2 y₁.2 y₂.2 hxx' hyy'
      h₁₁ h₁₂ h₂₁ h₂₂
      trivial trivial trivial trivial
  let fx : Fin 3 → XRole := fun i =>
    ⟨f (sx i), by
      have hi : Role Small 0 (sx i) := powerX_hasRole i
      exact hf.1.1 (0 : Fin 3) (fun _ => sx i) hi⟩
  let fy : Fin 3 → YRole := fun j =>
    ⟨f (sy j), by
      have hj : Role Small 1 (sy j) := powerY_hasRole j
      exact hf.1.1 (1 : Fin 3) (fun _ => sy j) hj⟩
  exact staircase_noSquare_obstruction R hNoSquare fx fy hDomain

end StructuralRamsey.Structure.NativePowerObstruction
