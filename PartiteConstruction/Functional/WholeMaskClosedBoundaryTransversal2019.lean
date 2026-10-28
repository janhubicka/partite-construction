import PartiteConstruction.Structure.PartialSetFunctionsClosed
import PartiteConstruction.Structure.PartialSetFunctionsTransversal
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019

/-!
# Genuine partial-function CLOSED boundaries retain output transversality

The verified two-pass 2019 profile proof transports a weak common root
to a CLOSED generated boundary of the real function base. To apply
the canonical complete-mask U-closed and embedding dictionaries to that
boundary, it must inherit fibre transversality by actual output parts.

A full closed inclusion preserves the ENTIRE Option(Set) function
value, including the genuine defined-empty case. Distinct outputs
of the closed substructure in one part therefore remain distinct,
as they were in the ambient source. No weak substructure is closed
or enlarged by this theorem; the source boundary is already closed.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Fibre transversality is hereditary on an ACTUAL
genuinely partial-function closed substructure, under the
unchanged inherited part map. -/
theorem FibreTransversal.induceClosed
    (A : PartialSetStructure L V)
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (hS : A.IsClosed S) :
    FibreTransversal (A.induceClosed S hS)
      (part ∘ Subtype.val) := by
  intro F xs U hSome y hy z hz heq
  have hMap := (A.closedInclusion S hS).map_func F xs
  rw [hSome] at hMap
  change some (Structure.imageSet Subtype.val U) =
    A.func F (Subtype.val ∘ xs) at hMap
  have hyImage : y.1 ∈ Structure.imageSet Subtype.val U :=
    ⟨y,hy,rfl⟩
  have hzImage : z.1 ∈ Structure.imageSet Subtype.val U :=
    ⟨z,hz,rfl⟩
  have hyz : y.1 = z.1 :=
    hTrans F (Subtype.val ∘ xs)
      (Structure.imageSet Subtype.val U) hMap.symm
      y.1 hyImage z.1 hzImage heq
  exact Subtype.ext hyz

/-- The canonical complete-mask expansion of EVERY already
function-closed boundary is itself 2019 U-closed. This is the
source-side boundary used by generated 2019 profile relations,
not a fictitious U-closed structure on an arbitrary weak test. -/
theorem wholeMaskTagExpansion_induceClosed_isUClosed
    (A : PartialSetStructure L V)
    (part : V → P) (hTrans : FibreTransversal A part)
    (S : Set V) (hS : A.IsClosed S) :
    IsUClosed (L.wholeMaskClosureRules P)
      (wholeMaskTagExpansion
        ((A.induceClosed S hS).wholeMaskPatternGraph
          (part ∘ Subtype.val))) :=
  (A.induceClosed S hS).wholeMaskTagExpansion_isUClosed
    (part ∘ Subtype.val)
    (hTrans.induceClosed A part S hS)

end StructuralRamsey.PartialSetStructure
