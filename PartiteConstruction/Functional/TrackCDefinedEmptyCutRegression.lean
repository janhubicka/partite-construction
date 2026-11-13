import PartiteConstruction.Structure.PartialSetFunctionsWholeFreeAmalgam
import PartiteConstruction.Structure.PartialSetFunctionsWholeGraph

/-!
# Appendix A Track C: defined-empty inputs cannot be discarded in free cuts

The rich genuine Option(Set) functional language distinguishes
  F(a,b) = some empty
from undefined F(a,b) = none.

An active mixed binary input blocks a genuine domain-aware functional
free amalgam even though its `collapseDomain` native set-valued
function is empty on EVERY input.

This is a finite regression for the exact missing premise when
applying a closed-native irreducibility -> tagged U-irreducibility
lemma to arbitrary rich PartialSetStructure examples. It does NOT
refute the already verified conditional bridge for native Structure
nor the original class-level local-completion theorem.

The whole native-to-OLD transfer requires a no-defined-empty
hypothesis or a different, domain-aware irreducibility dictionary.
-/


namespace StructuralRamsey.PartialSetStructure.TrackCDefinedEmptyCut

open StructuralRamsey

/-- Two-argument function and no primitive relations. -/
def binaryLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity := fun _ => 2

/-- The ONLY defined input is the mixed pair (0,1), with EMPTY value. -/
def mixedDefinedEmpty : PartialSetStructure binaryLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ xs =>
    if xs 0 = 0 ∧ xs 1 = 1 then some ∅ else none

/-- The mixed input is genuinely defined, despite having zero output vertices. -/
theorem mixedDefinedEmpty_on_cross :
    mixedDefinedEmpty.func () (fun i : Fin 2 => i) =
      some (∅ : Set (Fin 2)) := by
  simp [mixedDefinedEmpty]

/-- Definedness is detected by the independent Option domain bit. -/
theorem mixedDefinedEmpty_domain_cross :
    mixedDefinedEmpty.Defined () (fun i : Fin 2 => i) := by
  exact ⟨∅, mixedDefinedEmpty_on_cross⟩

/-- Every collapsed native function fibre is empty, including on the
original active mixed input. This is the information loss. -/
theorem mixedDefinedEmpty_collapse_all_empty
    (F : binaryLanguage.FuncSymbol) (xs : Fin 2 → Fin 2) :
    mixedDefinedEmpty.collapseDomain.func F xs =
      (∅ : Set (Fin 2)) := by
  change
    (if xs 0 = 0 ∧ xs 1 = 1 then
      some (∅ : Set (Fin 2)) else none).getD ∅ = ∅
  split_ifs <;> rfl

/-- Under GENUINE partial free-amalgamation semantics, the two singleton
sides can never cover the active mixed input. Works for ANY root and
full side embeddings with these actual singleton images; no special
side structures or synthetic closure hull are assumed. -/
theorem mixedDefinedEmpty_prevents_two_singleton_free_cut
    {RootV LeftV RightV : Type}
    {Root : PartialSetStructure binaryLanguage RootV}
    {Left : PartialSetStructure binaryLanguage LeftV}
    {Right : PartialSetStructure binaryLanguage RightV}
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (iL : Embedding Left mixedDefinedEmpty)
    (iR : Embedding Right mixedDefinedEmpty)
    (hLeft : ∀ x : LeftV, iL.toFun x = 0)
    (hRight : ∀ x : RightV, iR.toFun x = 1) :
    ¬ IsFreeAmalgam sL sR iL iR := by
  intro hFree
  rcases (hFree.defined_iff () (fun i : Fin 2 => i)).mp
      mixedDefinedEmpty_domain_cross with
    ⟨a, _ha, hEq⟩ | ⟨b, _hb, hEq⟩
  · have hContra : (1 : Fin 2) = 0 := by
      calc
        (1 : Fin 2) = (iL.toFun ∘ a) 1 := congrFun hEq 1
        _ = 0 := hLeft (a 1)
    exact (by decide : (1 : Fin 2) ≠ 0) hContra
  · have hContra : (0 : Fin 2) = 1 := by
      calc
        (0 : Fin 2) = (iR.toFun ∘ b) 0 := congrFun hEq 0
        _ = 1 := hRight (b 0)
    exact (by decide : (0 : Fin 2) ≠ 1) hContra

end StructuralRamsey.PartialSetStructure.TrackCDefinedEmptyCut
