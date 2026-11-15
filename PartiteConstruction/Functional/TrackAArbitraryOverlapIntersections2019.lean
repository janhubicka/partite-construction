import PartiteConstruction.Functional.TrackAActiveOverlapWeakProjection2019

/-!
# Track A: arbitrary intersections of active-cover exact weak Picture supports

The genuine native partite output criterion `ActiveWeakOutputPartCover`
is a local condition on function inputs and output part labels. It is
stable not only under binary exact intersections, but also under
ARBITRARY indexed intersections of covered supports (including an
empty indexing type, for which the support is the entire carrier).

Consequently an actual WeaklyPartiteOver native System retains its
original source-defined partial weak projection on the LITERAL common
vertex support of any indexed family of locally covered weak roots.

The exact preimage of such an intersection under a full
part-preserving copy embedding likewise has the native partial
weak projection. This is a source-map transport for overlapping
families of A-copies and generated root atlases; it does not create
or synchronize their target-side strict functional tree witnesses.

These statements are not asserted for unions, arbitrary EHN weak
projections as copy maps, or closure hulls replacing the tested set.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- The active-output-part cover condition is stable under arbitrary
indexed intersections of literal weak supports. The empty
intersection is the full vertex set, so no nonempty-index hypothesis
is needed. -/
theorem System.ActiveWeakOutputPartCover.iInter
    {I : Type*} (B : System L P V)
    (S : I → Set V)
    (hS : ∀ i, B.ActiveWeakOutputPartCover (S i)) :
    B.ActiveWeakOutputPartCover (⋂ i, S i) := by
  intro F xs hMeet y hy hPart
  apply Set.mem_iInter.mpr
  intro i
  let xs_i : Fin (L.funcArity F) → S i :=
    fun j => ⟨(xs j).1, (Set.mem_iInter.mp (xs j).2) i⟩
  have hMeet_i :
      ((B.toStructure.func F (Subtype.val ∘ xs_i)) ∩ S i).Nonempty := by
    obtain ⟨z, hzQ, hzAll⟩ := hMeet
    exact ⟨z, hzQ, (Set.mem_iInter.mp hzAll) i⟩
  have hPart_i : B.part y ∈ B.part '' S i := by
    obtain ⟨z, hzAll, hLabel⟩ := hPart
    exact ⟨z, (Set.mem_iInter.mp hzAll) i, hLabel⟩
  exact hS i F xs_i hMeet_i y hy hPart_i

/-- Any indexed intersection of locally covered literal weak
supports in a genuine native Picture has a correct ORIGINAL
source-defined weak projection into its precise occupied control
part-image, with no generated closure. -/
theorem System.iInter_originalPartialWeakProjection
    {I : Type*} (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : I → Set V)
    (hS : ∀ i, B.ActiveWeakOutputPartCover (S i)) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (⋂ i, S i))
      (D.weakInduce (B.part '' (⋂ i, S i)))
      (clippedWeakImageMap B.part (⋂ i, S i)) := by
  exact (B.arbitraryWeakImage_originalPartial_iff_activePartCover
    D hB (⋂ i, S i)).mpr
      (System.ActiveWeakOutputPartCover.iInter B S hS)

/-- Inverse image under a FULL functional part-preserving embedding
of an indexed exact intersection of locally covered target weak
supports is again a valid source-defined weak test. -/
theorem Embedding.iInter_preimage_originalPartialWeakProjection
    {I : Type*}
    {B : System L P V} {C : System L P W}
    (e : Embedding B C)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : I → Set W)
    (hS : ∀ i, C.ActiveWeakOutputPartCover (S i)) :
    Structure.IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (e.toFun ⁻¹' (⋂ i, S i)))
      (D.weakInduce (B.part '' (e.toFun ⁻¹' (⋂ i, S i))))
      (clippedWeakImageMap B.part (e.toFun ⁻¹' (⋂ i, S i))) := by
  exact e.preimage_originalPartialWeakProjection
    D hB (⋂ i, S i)
    (System.ActiveWeakOutputPartCover.iInter C S hS)

end StructuralRamsey.FunctionalPartite
