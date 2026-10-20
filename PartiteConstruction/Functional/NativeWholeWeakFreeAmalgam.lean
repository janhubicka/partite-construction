import PartiteConstruction.Structure.PartialSetFunctionsWholeFreeAmalgam
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Whole-value weak cuts of the existing genuine native functional construction

The existing native construction represents undefined applications by empty
fibres. Its domain convention is faithfully translated to `Option (Set V)`
by making exactly the nonempty fibres defined. This translation does not
assert that an arbitrary defined-empty structure arises from the old API.

Full native embeddings and full native free amalgams preserve this exact
translation. Consequently every actual native full attachment, restricted
to an arbitrary weak vertex test under the WHOLE-value convention, is a
full partial-functional free amalgam of its exact weak sides and root.

No output is clipped, no tested source vertex set is enlarged, and no
domain reflection is imposed on an external original-partial projection.
-/

namespace StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Faithfully expose the domain already used by the native construction:
a set-valued application is defined precisely when its fibre is nonempty.
The richer Option API may additionally have defined-empty applications. -/
noncomputable def toNonemptyPartial (A : Structure L V) :
    PartialSetStructure L V where
  rel := A.rel
  func F x := by
    classical
    exact if (A.func F x).Nonempty then some (A.func F x) else none

@[simp] theorem toNonemptyPartial_defined_iff
    (A : Structure L V) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    A.toNonemptyPartial.Defined F x ↔ (A.func F x).Nonempty := by
  classical
  by_cases h : (A.func F x).Nonempty
  · simp [PartialSetStructure.Defined, toNonemptyPartial, h]
  · simp [PartialSetStructure.Defined, toNonemptyPartial, h]

/-- Full native embeddings retain their full domain and whole-value
equations in the explicit partial-function language. -/
noncomputable def Embedding.toNonemptyPartial
    {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) :
    PartialSetStructure.Embedding A.toNonemptyPartial B.toNonemptyPartial where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    classical
    intro F x
    change
      (if (A.func F x).Nonempty then some (A.func F x) else none).map
        (imageSet e.toFun) =
      (if (B.func F (e.toFun ∘ x)).Nonempty then
        some (B.func F (e.toFun ∘ x)) else none)
    have hMap : imageSet e.toFun (A.func F x) =
        B.func F (e.toFun ∘ x) := e.map_func F x
    have hNonempty : (B.func F (e.toFun ∘ x)).Nonempty ↔
        (A.func F x).Nonempty := by
      rw [← hMap]
      constructor
      · rintro ⟨y, z, hz, _⟩
        exact ⟨z, hz⟩
      · rintro ⟨z, hz⟩
        exact ⟨e.toFun z, ⟨z, hz, rfl⟩⟩
    by_cases hA : (A.func F x).Nonempty
    · have hB := hNonempty.mpr hA
      simp only [hA, hB, if_pos, Option.map_some]
      exact congrArg some hMap
    · have hB : ¬ (B.func F (e.toFun ∘ x)).Nonempty := by
        intro h
        exact hA (hNonempty.mp h)
      simp [hA, hB]

/-- Every actual full native functional free-amalgam diagram also has
the independent domain no-crossing property in its faithful partial
presentation. For the native convention each defined application has
an output, and its incidence identifies the required source side. -/
theorem IsFreeAmalgam.toNonemptyPartial
    {H E F C : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    PartialSetStructure.IsFreeAmalgam
      sL.toNonemptyPartial sR.toNonemptyPartial
      iL.toNonemptyPartial iR.toNonemptyPartial := by
  constructor
  · exact hFree.covers
  · exact hFree.overlap
  · exact hFree.rel_iff
  · intro G x
    simp only [toNonemptyPartial_defined_iff]
    constructor
    · rintro ⟨y, hy⟩
      rcases (hFree.func_iff G x y).mp hy with
        ⟨a, b, hb, hx, _hy⟩ | ⟨a, b, hb, hx, _hy⟩
      · exact Or.inl ⟨a, ⟨b, hb⟩, hx⟩
      · exact Or.inr ⟨a, ⟨b, hb⟩, hx⟩
    · rintro (⟨a, ⟨b, hb⟩, hx⟩ | ⟨a, ⟨b, hb⟩, hx⟩)
      · refine ⟨iL b, ?_⟩
        exact (hFree.func_iff G x (iL b)).mpr
          (Or.inl ⟨a, b, hb, hx, rfl⟩)
      · refine ⟨iR b, ?_⟩
        exact (hFree.func_iff G x (iR b)).mpr
          (Or.inr ⟨a, b, hb, hx, rfl⟩)

/-- Exact source-side decomposition for the WHOLE-value weak test of
ANY genuine native full functional attachment.

The four new maps are full in the explicit partial-function language.
The weak common root is the literal inverse image of the tested vertices,
without assuming ambient closedness or adding generated vertices. -/
theorem IsFreeAmalgam.wholeWeakPartialInduce_withMaps
    {H E F C : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.toFun ∘ sL.toFun) ⁻¹' S
    ∃ (mL : PartialSetStructure.Embedding
          (PartialSetStructure.wholeWeakInduce Root.toNonemptyPartial Mset)
          (PartialSetStructure.wholeWeakInduce Left.toNonemptyPartial Lset))
      (mR : PartialSetStructure.Embedding
          (PartialSetStructure.wholeWeakInduce Root.toNonemptyPartial Mset)
          (PartialSetStructure.wholeWeakInduce Right.toNonemptyPartial Rset))
      (jL : PartialSetStructure.Embedding
          (PartialSetStructure.wholeWeakInduce Left.toNonemptyPartial Lset)
          (PartialSetStructure.wholeWeakInduce Whole.toNonemptyPartial S))
      (jR : PartialSetStructure.Embedding
          (PartialSetStructure.wholeWeakInduce Right.toNonemptyPartial Rset)
          (PartialSetStructure.wholeWeakInduce Whole.toNonemptyPartial S)),
      PartialSetStructure.IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL.toFun a).1 = iL a.1) ∧
      (∀ b : Rset, (jR.toFun b).1 = iR b.1) :=
  hFree.toNonemptyPartial.wholeWeakInduce_withMaps S

end StructuralRamsey.Structure
