import PartiteConstruction.Functional.TrackAWeakMapActiveCoverPullback2019

/-!
# Track A: stability of active weak output-part cover under exact intersections
# and full part-preserving embeddings

The exact original-partial projection criterion in the native functional
Picture is active-output-part cover on its LITERAL weak vertex support:
whenever the output value of a function input in S intersects S, every
output whose part label is occupied by S must itself lie in S.

Two closure principles needed for genuine partite-copy geometry:

1. Intersections: if S and T satisfy the local active-cover condition,
   then the exact weak intersection S∩T satisfies it. No generated hull
   or transfer to a larger intermediate carrier is used.
2. Full partite embeddings: if e:B↪C is a genuine FULL part-preserving
   embedding of functional Systems, and an exact target subset S satisfies
   active cover in C, then its LITERAL inverse image under e satisfies
   active cover in B. In contrast this is NOT asserted for a merely
   original-partial/EHN projection, which need not reflect undefined
   inputs or preserve whole output fibres.

These two stability properties can be used in gluing diagrams of exact
weak partite sides and roots. They do NOT assert that all arbitrary
weak roots satisfy active cover, nor construct strict B-tree completions
or solve the local ambient-relative class axiom.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Active output-part cover is closed under intersection of exact
vertex supports, with no finite-carrier or positive-arity assumption.
In particular this applies to common weak roots of copies whose
two side supports already satisfy active cover. -/
theorem System.ActiveWeakOutputPartCover.inter
    (B : System L P V) (S T : Set V)
    (hS : B.ActiveWeakOutputPartCover S)
    (hT : B.ActiveWeakOutputPartCover T) :
    B.ActiveWeakOutputPartCover (S ∩ T) := by
  intro F xs hMeet y hy hPart
  let xsS : Fin (L.funcArity F) → S :=
    fun i => ⟨(xs i).1, (xs i).2.1⟩
  let xsT : Fin (L.funcArity F) → T :=
    fun i => ⟨(xs i).1, (xs i).2.2⟩
  have hMeetS :
      ((B.toStructure.func F (Subtype.val ∘ xsS)) ∩ S).Nonempty := by
    obtain ⟨a, ha, haST⟩ := hMeet
    exact ⟨a, ha, haST.1⟩
  have hMeetT :
      ((B.toStructure.func F (Subtype.val ∘ xsT)) ∩ T).Nonempty := by
    obtain ⟨a, ha, haST⟩ := hMeet
    exact ⟨a, ha, haST.2⟩
  have hPartS : B.part y ∈ B.part '' S := by
    obtain ⟨a, haST, haPart⟩ := hPart
    exact ⟨a, haST.1, haPart⟩
  have hPartT : B.part y ∈ B.part '' T := by
    obtain ⟨a, haST, haPart⟩ := hPart
    exact ⟨a, haST.2, haPart⟩
  exact ⟨hS F xsS hMeetS y hy hPartS,
    hT F xsT hMeetT y hy hPartT⟩

/-- Exact preimage of active-output-part cover under a TRUE FULL
part-preserving functional embedding. The proof now follows immediately
from the stronger positive-weak-map pullback theorem: neither complete
fibre equality nor reflection is needed for THIS source invariant. -/
theorem Embedding.preimage_activeWeakOutputPartCover
    {B : System L P V} {C : System L P W}
    (e : Embedding B C) (S : Set W)
    (hS : C.ActiveWeakOutputPartCover S) :
    B.ActiveWeakOutputPartCover (e.toFun ⁻¹' S) := by
  exact System.ActiveWeakOutputPartCover.preimage_weakHom
    B C e.toFun e.map_part e.toEmbedding.isWeakHomomorphism S hS

/-- In particular, inverse images of canonical selected supports
along honest full part-preserving copy embeddings satisfy the local
active-cover criterion on their ORIGINAL source vertices. -/
theorem Embedding.selectedSupport_preimage_activeWeakOutputPartCover
    {B : System L P V} {C : System L P W}
    (e : Embedding B C) {Q : Type v} (α : Q ↪ P) :
    B.ActiveWeakOutputPartCover (e.toFun ⁻¹' C.support α) :=
  e.preimage_activeWeakOutputPartCover
    (C.support α) (C.support_activeWeakOutputPartCover α)

end StructuralRamsey.FunctionalPartite
