import PartiteConstruction.Ramsey.ClosurePowerProtected
import PartiteConstruction.Ramsey.ClosureSemiClosed2019

/-! # Powers of exact nonclosed restrictions

The restricted old picture in the recursive repair need not be closed.
Do not apply the closed-base power theorem directly to that restriction.
Instead embed its native power into the power of the WHOLE closed old
picture and factor the protected part projection through the selected
induced part structure. Neither that control nor the support is assumed
closed. Separately, every positive native power of a semi-closed system
is semi-closed; missing closure outputs are not supplied by this theorem.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P Q V : Type v} {N : ℕ}

/-- Forget the subtype coordinates of an exact part restriction.
This embeds the actual restricted power into the whole power, after
relabelling its tags. No closure or positivity hypothesis is needed. -/
def restrictedPowerEmbedding (B : System L P V) (alpha : Q ↪ P) (N : ℕ) :
    Partite.Embedding ((power (B.restrict alpha) N).relabel alpha) (power B N) where
  toFun x := {
    part := alpha x.part
    coord := fun k => (x.coord k).1
    belongs := by
      intro k
      calc
        B.part (x.coord k).1 = alpha ((B.restrict alpha).part (x.coord k)) :=
          (B.restrictedPart_spec alpha (x.coord k)).symm
        _ = alpha x.part := congrArg alpha (x.belongs k)
  }
  injective := by
    intro x y h
    apply NonInduced.Vertex.ext (B.restrict alpha)
    · exact alpha.injective (congrArg NonInduced.Vertex.part h)
    · intro k
      apply Subtype.ext
      exact congrArg (fun z : Vertex B N => z.coord k) h
  map_rel_iff := fun _ _ => Iff.rfl
  map_part := fun _ => rfl

/-- The restricted power is protected even if the restriction itself
is NOT closed. The ambient old picture is closed; the control need not be. -/
theorem restricted_power_part_protected
    {rules : ClosureDescription L} {A : RelStructure L Q} {D : RelStructure L P}
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hB : IsUClosed rules B.toRelStructure)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part)
    (hN : 0 < N) :
    IsClosedUHomomorphismEmbedding rules
      (power (B.restrict alpha.toFunctionEmbedding) N).toRelStructure A
      (power (B.restrict alpha.toFunctionEmbedding) N).part := by
  let R := power (B.restrict alpha.toFunctionEmbedding) N
  let e := (restrictedPowerEmbedding B alpha.toFunctionEmbedding N).toEmbedding
  have hWhole := (power_part_protected B hB hPart hN).precomp_embedding e
  constructor
  · intro S z hz
    exact (alpha.map_rel_iff S (R.part ∘ z)).mp (hWhole.1 S z hz)
  · intro X Test hClosed hIrred a
    obtain ⟨d, hd⟩ := hWhole.on_test Test hClosed hIrred a
    have hRange (x : X) : ∃ q : Q, d x = alpha q :=
      ⟨R.part (a x), hd x⟩
    refine ⟨d.factorThroughRange alpha hRange, ?_⟩
    intro x
    apply alpha.injective
    exact (Classical.choose_spec (hRange x)).symm.trans (hd x)

/-- Partial root validity and uniqueness are preserved coordinatewise.
The positive exponent is needed for root reflection and tag equality. -/
theorem power_isUSemiClosed
    {rules : ClosureDescription L}
    (B : System L P V) (hB : IsUSemiClosed rules B.toRelStructure)
    (hN : 0 < N) : IsUSemiClosed rules (power B N).toRelStructure := by
  classical
  let k0 : Fin N := ⟨0, hN⟩
  intro rule hrule
  constructor
  · intro t ht
    have hRoots : ∀ k : Fin N, ∃ r : RelStructure.Embedding rule.root B.toRelStructure,
        ∀ i : Fin rule.rootSize, (t (i.castLE rule.rootLE)).coord k = r i := by
      intro k
      exact (hB rule hrule).1 (fun j => (t j).coord k) (ht k)
    let r (k : Fin N) : RelStructure.Embedding rule.root B.toRelStructure :=
      Classical.choose (hRoots k)
    have hr (k : Fin N) (i : Fin rule.rootSize) :
        (t (i.castLE rule.rootLE)).coord k = r k i :=
      Classical.choose_spec (hRoots k) i
    let e : RelStructure.Embedding rule.root (power B N).toRelStructure := {
      toFun := fun i => t (i.castLE rule.rootLE)
      injective := by
        intro i j hij
        apply (r k0).injective
        exact (hr k0 i).symm.trans
          ((congrArg (fun x : Vertex B N => x.coord k0) hij).trans (hr k0 j))
      map_rel_iff := by
        intro S z
        constructor
        · intro hz
          have hCoord : B.rel S
              (fun j => (t ((z j).castLE rule.rootLE)).coord k0) := hz k0
          have hEq : (fun j => (t ((z j).castLE rule.rootLE)).coord k0) =
              r k0 ∘ z := funext (fun j => hr k0 (z j))
          apply ((r k0).map_rel_iff S z).mp
          rw [← hEq]
          exact hCoord
        · intro hz k
          have hCoord := ((r k).map_rel_iff S z).mpr hz
          have hEq : (fun j => (t ((z j).castLE rule.rootLE)).coord k) =
              r k ∘ z := funext (fun j => hr k (z j))
          change B.rel S (fun j => (t ((z j).castLE rule.rootLE)).coord k)
          rw [hEq]
          exact hCoord
    }
    exact ⟨e, fun _ => rfl⟩
  · intro t s ht hs hRoot
    have hCoords (k : Fin N) : (fun j => (t j).coord k) = (fun j => (s j).coord k) := by
      apply (hB rule hrule).2 _ _ (ht k) (hs k)
      intro i
      exact congrArg (fun x : Vertex B N => x.coord k) (hRoot i)
    funext j
    apply NonInduced.Vertex.ext B
    · exact ((t j).belongs k0).symm.trans
        ((congrArg B.part (congrFun (hCoords k0) j)).trans ((s j).belongs k0))
    · intro k
      exact congrFun (hCoords k) j

end StructuralRamsey.Partite.Induced
