import PartiteConstruction.Functional.PartialClippedWeakOriginalPreimage2019
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff
import PartiteConstruction.Functional.LegacyWeakPartialCommutation2019

/-!
# Track A: original 2019 source-defined clipped weak projections in native functional language

The printed Nešetřil-programme survey works with `Structure L V`,
where a nonempty set-valued function fibre is defined and an empty
fibre encodes an undefined input. Its `weakInduce` clips output sets.

The earlier verified dictionary
`originalPartialHom_iff_nonemptyPartial` identifies exactly these
source-defined native maps with genuinely partial `Option(Set)` maps,
on the SAME carriers and vertex function. Separately,
`toNonemptyPartial_weakInduce_commute` identifies the printed native
clipped restriction with the genuine partial clipped restriction.

Compose these verified correspondences with Track A's exact preimage
restriction theorem. This proves the direct ORIGINAL NATIVE statement
without deriving an unsupported domain-reflecting/total-fibre equation.

No singleton-valuedness, injectivity, positive-arity restriction,
extra vertices or generator-hull enlargement is used. The selected
partite-support corollary requires literal saturation under fibres
of the projection. This does not prove the missing strict functional
mixed-root B-tree completion nor arbitrary ambient local transfer.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- An original-2019 source-defined partial homomorphism of native
set-valued structures restricts to the exact CLIPPED weak preimage
of a target vertex cut, on literally the original map. The source
map need not reflect undefined inputs and can identify vertices. -/
theorem IsOriginalPartialHomomorphism.clippedWeakRestrictToPreimage
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (T : Set W) :
    IsOriginalPartialHomomorphism
      (A.weakInduce (f ⁻¹' T)) (B.weakInduce T)
      (PartialSetStructure.restrictMap f T) := by
  have hPartial :
      PartialSetStructure.IsOriginalPartialHomomorphism
        A.toNonemptyPartial B.toNonemptyPartial f :=
    TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mp hf
  have hPre := hPartial.clippedWeakRestrictToPreimage T
  rw [← toNonemptyPartial_weakInduce_commute A (f ⁻¹' T),
      ← toNonemptyPartial_weakInduce_commute B T] at hPre
  exact TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mpr hPre

/-- The projected exact image theorem in the ORIGINAL NATIVE
set-valued functional language. On a source support S which is
exactly saturated under fibres of f, restriction to f[S] preserves
every surviving defined complete function value. -/
theorem IsOriginalPartialHomomorphism.clippedWeakImage_of_saturated
    {A : Structure L V} {B : Structure L W} {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (S : Set V)
    (hSat : ∀ x : V, f x ∈ f '' S → x ∈ S) :
    IsOriginalPartialHomomorphism
      (A.weakInduce S) (B.weakInduce (f '' S))
      (fun x : S => (⟨f x.1, ⟨x.1, x.2, rfl⟩⟩ : f '' S)) := by
  have hPartial :
      PartialSetStructure.IsOriginalPartialHomomorphism
        A.toNonemptyPartial B.toNonemptyPartial f :=
    TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mp hf
  have hImage := hPartial.clippedWeakImage_of_saturated S hSat
  rw [← toNonemptyPartial_weakInduce_commute A S,
      ← toNonemptyPartial_weakInduce_commute B (f '' S)] at hImage
  exact TrackESourceDefinedPartialIff.originalPartialHom_iff_nonemptyPartial.mpr hImage

end StructuralRamsey.Structure
