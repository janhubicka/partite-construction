import PartiteConstruction.Functional.Closed
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Closure in an arbitrary free-amalgam diagram

One relation-locality argument proves both closure observations used in the
survey's recursive construction. No finiteness, transversality, or positive
function-arity hypothesis is needed. In particular these local statements
also handle constants; the positive-arity restriction belongs to the initial
disjoint-union construction, not to the closure calculus.
-/
namespace StructuralRamsey.RelStructure

open Structure

universe u v
variable {L : Language.{u}} {U V W X : Type v}

namespace Embedding

/-- The inverse image of a function-closed set under an induced embedding is
function-closed. The embedding itself need not be closed. -/
theorem functionClosedSet_preimage
    {A : RelStructure L.graph V} {B : RelStructure L.graph W}
    (e : Embedding A B) {S : Set W} (hS : FunctionClosedSet B S) :
    FunctionClosedSet A (e ⁻¹' S) := by
  intro F x y hy hx
  apply hS F (e ∘ x) (e y)
  · have hmap := (e.map_rel_iff (.inr F) (funcTuple x y)).mpr hy
    exact Eq.mp
      (congrArg (fun t => B.rel (.inr F) t)
        (Structure.comp_funcTuple (e : V → W) x y)) hmap
  · exact hx

/-- Closedness of an induced embedding is exactly closedness of its range. -/
theorem functionClosed_iff_range
    {A : RelStructure L.graph V} {B : RelStructure L.graph W}
    (e : Embedding A B) :
    FunctionClosedMap A B e ↔ FunctionClosedSet B (Set.range e) := by
  classical
  constructor
  · intro h F x y hy hx
    choose z hz using hx
    have heq : e ∘ z = x := funext hz
    have hy' : B.rel (.inr F) (funcTuple (e ∘ z) y) := by
      rw [heq]
      exact hy
    obtain ⟨a, _, ha⟩ := h F z y hy'
    exact ⟨a, ha⟩
  · intro h F x y hy
    obtain ⟨z, hz⟩ := h F (e ∘ x) y hy (fun i => ⟨x i, rfl⟩)
    refine ⟨z, ?_, hz⟩
    apply (e.map_rel_iff (.inr F) (funcTuple x z)).mp
    have ht : e ∘ funcTuple x z = funcTuple (e ∘ x) y :=
      (Structure.comp_funcTuple (e : V → W) x z).trans
        (congrArg (funcTuple (e ∘ x)) hz)
    exact Eq.mpr (congrArg (fun t => B.rel (.inr F) t) ht) hy

end Embedding

namespace IsFreeAmalgam

variable {D : RelStructure L.graph U} {A : RelStructure L.graph V}
variable {B : RelStructure L.graph W} {C : RelStructure L.graph X}
variable {fA : Embedding D A} {fB : Embedding D B}
variable {iA : Embedding A C} {iB : Embedding B C}

/-- A set is closed in a free amalgam iff its inverse image in each side is
closed. Only the relation-locality field of the free-amalgam diagram is used. -/
theorem functionClosedSet_iff
    (hfree : IsFreeAmalgam fA fB iA iB) (S : Set X) :
    FunctionClosedSet C S ↔
      FunctionClosedSet A (iA ⁻¹' S) ∧
      FunctionClosedSet B (iB ⁻¹' S) := by
  constructor
  · intro hS
    exact ⟨iA.functionClosedSet_preimage hS,
      iB.functionClosedSet_preimage hS⟩
  · rintro ⟨hA, hB⟩ F x y hy hx
    rcases (hfree.rel_iff (.inr F) (funcTuple x y)).mp hy with
      ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · have hxmap (k : Fin (L.funcArity F)) :
          x k = iA (t k.castSucc) := by
        calc
          x k = funcTuple x y k.castSucc :=
            (Structure.funcTuple_castSucc x y k).symm
          _ = iA (t k.castSucc) := congrFun heq k.castSucc
      have hymap : y = iA (t (Fin.last (L.funcArity F))) := by
        calc
          y = funcTuple x y (Fin.last (L.funcArity F)) :=
            (Structure.funcTuple_last x y).symm
          _ = iA (t (Fin.last (L.funcArity F))) :=
            congrFun heq (Fin.last (L.funcArity F))
      rw [hymap]
      apply hA F (fun k => t k.castSucc) (t (Fin.last (L.funcArity F)))
      · exact Eq.mpr
          (congrArg (fun q => A.rel (.inr F) q)
            (Structure.funcTuple_eta t)) ht
      · intro k
        change iA (t k.castSucc) ∈ S
        rw [← hxmap k]
        exact hx k
    · have hxmap (k : Fin (L.funcArity F)) :
          x k = iB (t k.castSucc) := by
        calc
          x k = funcTuple x y k.castSucc :=
            (Structure.funcTuple_castSucc x y k).symm
          _ = iB (t k.castSucc) := congrFun heq k.castSucc
      have hymap : y = iB (t (Fin.last (L.funcArity F))) := by
        calc
          y = funcTuple x y (Fin.last (L.funcArity F)) :=
            (Structure.funcTuple_last x y).symm
          _ = iB (t (Fin.last (L.funcArity F))) :=
            congrFun heq (Fin.last (L.funcArity F))
      rw [hymap]
      apply hB F (fun k => t k.castSucc) (t (Fin.last (L.funcArity F)))
      · exact Eq.mpr
          (congrArg (fun q => B.rel (.inr F) q)
            (Structure.funcTuple_eta t)) ht
      · intro k
        change iB (t k.castSucc) ∈ S
        rw [← hxmap k]
        exact hx k

/-- The part of the left side lying in the right side is its overlap. -/
theorem left_preimage_right_range
    (hfree : IsFreeAmalgam fA fB iA iB) :
    iA ⁻¹' Set.range iB = Set.range fA := by
  ext a
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨d, ha, _⟩ := (hfree.overlap a b).mp hb.symm
    exact ⟨d, ha.symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨fB d, ((hfree.overlap (fA d) (fB d)).mpr ⟨d, rfl, rfl⟩).symm⟩

/-- The symmetric overlap identity. -/
theorem right_preimage_left_range
    (hfree : IsFreeAmalgam fA fB iA iB) :
    iB ⁻¹' Set.range iA = Set.range fB := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨d, _, hb⟩ := (hfree.overlap a b).mp ha
    exact ⟨d, hb.symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨fA d, (hfree.overlap (fA d) (fB d)).mpr ⟨d, rfl, rfl⟩⟩

/-- The left side is closed precisely when the overlap is closed in the
right side. No assumption about closedness in the left side is needed. -/
theorem left_closed_iff
    (hfree : IsFreeAmalgam fA fB iA iB) :
    FunctionClosedMap A C iA ↔ FunctionClosedMap D B fB := by
  rw [iA.functionClosed_iff_range, fB.functionClosed_iff_range,
    hfree.functionClosedSet_iff, hfree.right_preimage_left_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro F x y hy hx
    exact ⟨y, rfl⟩

/-- The right side is closed precisely when the overlap is closed in the
left side. -/
theorem right_closed_iff
    (hfree : IsFreeAmalgam fA fB iA iB) :
    FunctionClosedMap B C iB ↔ FunctionClosedMap D A fA := by
  rw [iB.functionClosed_iff_range, fA.functionClosed_iff_range,
    hfree.functionClosedSet_iff, hfree.left_preimage_right_range]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro F x y hy hx
    exact ⟨y, rfl⟩

/-- Survey Observation `obs:disaster2`, including the converse. -/
theorem sides_closed_iff
    (hfree : IsFreeAmalgam fA fB iA iB) :
    (FunctionClosedMap A C iA ∧ FunctionClosedMap B C iB) ↔
      (FunctionClosedMap D A fA ∧ FunctionClosedMap D B fB) := by
  rw [hfree.left_closed_iff, hfree.right_closed_iff]
  exact and_comm

/-- Survey Observation `obs:solution`: a subset of the common root is closed
in the amalgam iff its images are closed in both sides. Neither the full root
nor either side has to be closed. -/
theorem common_image_closed_iff
    (hfree : IsFreeAmalgam fA fB iA iB) (S : Set U) :
    FunctionClosedSet C ((iA ∘ fA) '' S) ↔
      FunctionClosedSet A (fA '' S) ∧ FunctionClosedSet B (fB '' S) := by
  have hcomm (d : U) : iA (fA d) = iB (fB d) :=
    (hfree.overlap (fA d) (fB d)).mpr ⟨d, rfl, rfl⟩
  have hleft : iA ⁻¹' ((iA ∘ fA) '' S) = fA '' S := by
    ext a
    constructor
    · rintro ⟨d, hd, heq⟩
      exact ⟨d, hd, iA.injective heq⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
  have hright : iB ⁻¹' ((iA ∘ fA) '' S) = fB '' S := by
    ext b
    constructor
    · rintro ⟨d, hd, heq⟩
      refine ⟨d, hd, ?_⟩
      apply iB.injective
      exact (hcomm d).symm.trans heq
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, hcomm d⟩
  rw [hfree.functionClosedSet_iff, hleft, hright]

end IsFreeAmalgam
end StructuralRamsey.RelStructure
