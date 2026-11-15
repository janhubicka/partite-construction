import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Track A: direct selected-support calculus in native functional Pictures

A selected support is EXACTLY the inverse image of a set of control
part labels. Its pullback along any vertex map preserving part labels
is therefore the original selected support, independently of
function-fibre preservation, injection, or the EHN projection axiom.

Moreover, an arbitrary intersection of part-saturated vertex sets
is again part-saturated. Thus the intersection of ANY collection of
selected supports is part-saturated and has the already verified
original source-defined weak part projection in any native
WeaklyPartiteOver system.

These direct arguments are materially shorter than invoking the
general active-output-part cover and full-embedding pullback chain
when the supports are SELECTED. Retain that broader chain for
arbitrary weak sets, where part saturation is genuinely absent.

No partite construction step is replaced; no strict B-tree target
witness or 2019 ambient local completion is claimed.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Arbitrary intersections of exact part-saturated native vertex
supports are part-saturated (including the empty intersection). -/
theorem System.PartSaturated.iInter
    {I : Type*} (B : System L P V) (S : I → Set V)
    (hS : ∀ i, B.PartSaturated (S i)) :
    B.PartSaturated (⋂ i, S i) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  apply Set.mem_iInter.mpr
  intro i
  exact hS i y ⟨x, (Set.mem_iInter.mp hx) i, hxy⟩

/-- Selected part supports pull back exactly under ANY part-preserving
vertex map. No functional embedding, injectivity or EHN control
hypothesis is needed for this set-theoretic identity. -/
theorem System.preimage_support_of_map_part
    (B : System L P V) (C : System L P W)
    (f : V → W)
    (hPart : ∀ x, C.part (f x) = B.part x)
    {Q : Type v} (α : Q ↪ P) :
    f ⁻¹' C.support α = B.support α := by
  ext x
  change C.part (f x) ∈ Set.range α ↔ B.part x ∈ Set.range α
  rw [hPart x]

/-- In particular, FULL native partite embeddings pull selected
control supports back to exactly the corresponding selected source
support, not merely to a support satisfying active fibre cover. -/
theorem Embedding.preimage_support
    {B : System L P V} {C : System L P W}
    (e : Embedding B C)
    {Q : Type v} (α : Q ↪ P) :
    e.toFun ⁻¹' C.support α = B.support α :=
  System.preimage_support_of_map_part B C e.toFun e.map_part α

/-- An indexed intersection of canonical selected supports in a
native System remains part-saturated by a purely part-label argument.
It does NOT use active-output-part masks, positivity of function
arities, or any closure properties of the weak support. -/
theorem System.selectedSupport_iInter_partSaturated
    {I : Type*} (B : System L P V)
    {Q : Type v} (α : I → (Q ↪ P)) :
    B.PartSaturated (⋂ i, B.support (α i)) :=
  System.PartSaturated.iInter B
    (fun i => B.support (α i))
    (fun i => B.support_partSaturated (α i))

end StructuralRamsey.FunctionalPartite
