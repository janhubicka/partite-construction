import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness

/-!
# Track E: every full genuine Option(Set) embedding descends to a full native embedding

The genuine partial-function language distinguishes undefined (none)
from defined-empty (some ∅). Collapsing this domain bit yields the
native set-valued-function representation. A FULL embedding preserves
the entire Option value, hence after dropping the domain bit still
preserves/refects primitive relations and maps every complete output
fibre onto the entire target output fibre.

No no-defined-empty hypothesis is required, because we are only
FORGETTING information, not reconstructing the original partial
structure. The underlying vertex map and carrier are identical.
This is the generic semantic final step for converting the full
partial-function exact-test copy obtained in Appendix A Track E
back into a full native function-language copy.
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- A full genuine partial-function embedding induces a full native
set-valued-function embedding on EXACTLY the same underlying vertex
map and carrier, including nullary inputs and multivalued/empty
outputs. It does not assert the inverse faithful reconstruction. -/
noncomputable def collapseDomain
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : PartialSetStructure.Embedding A B) :
    Structure.Embedding A.collapseDomain B.collapseDomain where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    intro F xs
    have h := congrArg
      (fun o : Option (Set W) => o.getD ∅)
      (e.map_func F xs)
    change Structure.imageSet e.toFun ((A.func F xs).getD ∅) =
      (B.func F (e.toFun ∘ xs)).getD ∅
    simpa only
      [StructuralRamsey.Structure.TrackENativePartialFullFaithfulness.option_getD_image]
      using h

/-- The collapse does not alter the selected full embedding's vertex map. -/
@[simp] theorem collapseDomain_apply
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : PartialSetStructure.Embedding A B) (x : V) :
    (e.collapseDomain).toFun x = e.toFun x := rfl

end StructuralRamsey.PartialSetStructure.Embedding
