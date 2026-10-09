import PartiteConstruction.Functional.NativePowerOrderedThird

/-! # Native HJ power obstruction with a hereditarily irreducible base

The ordered seven-vertex source is a genuine strict full-functional tree,
and its EHN part projection is verified in NativePowerOrderedThird.
The ordered three-vertex base has a hereditarily irreducible function
graph by NativePowerOrderedTarget.

The original and ordered systems have exactly the same parts and function
fibres. Thus their tagged coordinatewise powers have canonically
equivalent vertex types and *isomorphic full functional reducts*.
This transfers the verified staircase obstruction without inventing an
unrelated Cartesian power or taking a closure hull of the weak image.

The original 2019 partial-function homomorphism convention is strictly
weaker than the full-total-fibre convention addressed here.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

/-- Every inherited order tuple strictly increases the part label.
In particular no relation tuple can repeat a part. -/
theorem oldStageOrder_part_lt :
    ∀ a b : Fin 7,
      oldStageOrder a b → oldPart a < oldPart b := by
  decide

def oldOrderedSystem :
    FunctionalPartite.System toyLanguage.withLinearOrder (Fin 3) (Fin 7) where
  toStructure := oldStageOrdered
  part := oldPart
  relTransversal := by
    intro R x hx i j hp
    cases R with
    | inl R =>
        exact oldSystem.relTransversal R x hx i j hp
    | inr u =>
        cases u
        change (Fin 2 → Fin 7) at x
        change Fin 2 at i
        change Fin 2 at j
        change oldStageOrder (x 0) (x 1) at hx
        have hlt : oldPart (x 0) < oldPart (x 1) :=
          oldStageOrder_part_lt _ _ hx
        fin_cases i <;> fin_cases j
        · rfl
        · exact ((ne_of_lt hlt) hp).elim
        · exact ((ne_of_lt hlt) hp.symm).elim
        · rfl
  funcTransversal := by
    intro F x y z hy hz hp
    exact oldSystem.funcTransversal F x y z hy hz hp

theorem oldOrderedSystem_weaklyPartiteOver :
    oldOrderedSystem.WeaklyPartiteOver toyBaseOrdered :=
  oldStageOrdered_projection

abbrev OrderedPowerVertex :=
  FunctionalPartite.Induced.Vertex oldOrderedSystem 2

def actualOrderedPower : Structure toyLanguage.withLinearOrder
    OrderedPowerVertex :=
  (FunctionalPartite.Induced.power oldOrderedSystem 2).toStructure

theorem actualOrderedPower_weaklyPartiteOver :
    (FunctionalPartite.Induced.power oldOrderedSystem 2).WeaklyPartiteOver
      toyBaseOrdered :=
  FunctionalPartite.Induced.power_weaklyPartiteOver
    oldOrderedSystem_weaklyPartiteOver (by omega)

/-- Copy the part and coordinate data between two native tagged powers.
Proof fields are transported, not reconstructed by a generated closure. -/
def orderedVertexEquiv : PowerVertex ≃ OrderedPowerVertex where
  toFun v := {
    part := v.part
    coord := v.coord
    belongs := v.belongs
  }
  invFun v := {
    part := v.part
    coord := v.coord
    belongs := v.belongs
  }
  left_inv := by
    intro v
    cases v
    rfl
  right_inv := by
    intro v
    cases v
    rfl

/-- Forgetting the extra binary relation from the ordered native power
recovers the original native power *up to the canonical full embedding*
which is bijective on vertices. Full preservation includes empty fibres. -/
def oldPower_into_orderedReduct :
    Embedding actualPower actualOrderedPower.linearOrderReduct where
  toFun := orderedVertexEquiv
  injective := orderedVertexEquiv.injective
  map_rel_iff := by
    intro R x
    rfl
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hy
      refine ⟨orderedVertexEquiv.symm y, ?_, ?_⟩
      · exact hy
      · exact orderedVertexEquiv.apply_symm_apply y

/-- The full-total-fibre obstruction survives in the *actual* tagged
power of the expanded stage whose graph-base is hereditarily
irreducible. -/
theorem actualOrderedPower_no_fullStrictTreeHom
    {W : Type} {T : Structure toyLanguage.withLinearOrder W}
    (hTree : TreeAmalgam toyBaseOrdered W T)
    (f : OrderedPowerVertex → W)
    (hf : actualOrderedPower.IsHomomorphism T f) : False := by
  have hfRed :
      actualOrderedPower.linearOrderReduct.IsHomomorphism
        T.linearOrderReduct f := by
    constructor
    · intro R x hx
      exact hf.1 (.inl R) x hx
    · exact hf.2
  have hOld :
      actualPower.IsHomomorphism T.linearOrderReduct
        (f ∘ orderedVertexEquiv) :=
    hfRed.comp oldPower_into_orderedReduct.isHomomorphism
  exact actualPower_no_fullOrderedStrictTreeHom hTree
    (f ∘ orderedVertexEquiv) hOld

theorem actualOrderedPower_no_fullStrictTreeCompletion :
    ¬ HasTreeCompletion toyBaseOrdered actualOrderedPower := by
  rintro ⟨W,T,hTree,f,hf⟩
  exact actualOrderedPower_no_fullStrictTreeHom hTree f hf.1

end StructuralRamsey.Structure.NativePowerObstruction
