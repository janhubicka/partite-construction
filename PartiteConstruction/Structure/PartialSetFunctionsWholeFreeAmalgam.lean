import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Exact whole-value weak cuts of genuine partial functional free amalgams

This module uses partial functions with values in `Option (Set V)`.
An application is removed from a weak set as soon as any output escapes;
an originally defined empty value remains defined. The source sets below
are exact inverse images, and need not be closed in their ambient structures.

Freeness includes the independent function DOMAIN relation. Full side maps
already preserve every complete Option value, so domain localization also
localizes each entire function value. An incidence-only no-crossing condition
would incorrectly allow a crossing application with value `some ∅`.

The theorem gives the actual source weak-cut decomposition. It does not
construct compatible tree completions of the two sides.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}}
variable {V : Type v} {W : Type w}

/-- Full partial-function embeddings reflect definedness, including
defined empty values. This statement is not asserted for original-partial
homomorphisms, which need not reflect an undefined source input. -/
theorem Embedding.whole_defined_iff
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V) :
    B.Defined F (e.toFun ∘ x) ↔ A.Defined F x := by
  constructor
  · rintro ⟨T, hT⟩
    cases hA : A.func F x with
    | none =>
        have hMap := e.map_func F x
        rw [hA, Option.map_none, hT] at hMap
        cases hMap
    | some U =>
        exact ⟨U, hA⟩
  · rintro ⟨U, hU⟩
    refine ⟨Structure.imageSet e.toFun U, ?_⟩
    simpa only [hU, Option.map_some] using (e.map_func F x).symm

/-- A whole-value weak application can be defined only if its ambient
application is defined. The converse requires all ambient outputs to remain. -/
theorem wholeWeakInduce_defined_ambient
    (A : PartialSetStructure L V) (S : Set V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → S) :
    (wholeWeakInduce A S).Defined F x →
      A.Defined F (Subtype.val ∘ x) := by
  rintro ⟨T, hT⟩
  cases hA : A.func F (Subtype.val ∘ x) with
  | none =>
      simp [wholeWeakInduce, wholeWeakValue, hA] at hT
  | some U =>
      exact ⟨U, hA⟩

/-- A full free amalgam of genuinely partial set-valued structures.

The last field excludes crossing DEFINED applications, including applications
with empty value. The four displayed maps are full embeddings and therefore
also preserve and reflect the complete Option-valued fibres. -/
structure IsFreeAmalgam
    {H E F C : Type v}
    {Root : PartialSetStructure L H}
    {Left : PartialSetStructure L E}
    {Right : PartialSetStructure L F}
    {Whole : PartialSetStructure L C}
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (iL : Embedding Left Whole) (iR : Embedding Right Whole) : Prop where
  covers : ∀ z : C, (∃ a : E, z = iL.toFun a) ∨
    (∃ b : F, z = iR.toFun b)
  overlap : ∀ a : E, ∀ b : F,
    iL.toFun a = iR.toFun b ↔
      ∃ d : H, a = sL.toFun d ∧ b = sR.toFun d
  rel_iff : ∀ R z,
    Whole.rel R z ↔
      (∃ x : Fin (L.relArity R) → E,
        Left.rel R x ∧ z = iL.toFun ∘ x) ∨
      (∃ x : Fin (L.relArity R) → F,
        Right.rel R x ∧ z = iR.toFun ∘ x)
  defined_iff : ∀ G x,
    Whole.Defined G x ↔
      (∃ a : Fin (L.funcArity G) → E,
        Left.Defined G a ∧ x = iL.toFun ∘ a) ∨
      (∃ a : Fin (L.funcArity G) → F,
        Right.Defined G a ∧ x = iR.toFun ∘ a)

/-- The domain no-crossing law and full side embeddings localize every
COMPLETE defined value, including `some ∅`. Thus the preceding interface
has the whole-fibre law of a genuine partial functional free amalgam. -/
theorem IsFreeAmalgam.func_iff
    {H E F C : Type v}
    {Root : PartialSetStructure L H}
    {Left : PartialSetStructure L E} {Right : PartialSetStructure L F}
    {Whole : PartialSetStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (G : L.FuncSymbol) (x : Fin (L.funcArity G) → C) (T : Set C) :
    Whole.func G x = some T ↔
      (∃ a : Fin (L.funcArity G) → E, ∃ U : Set E,
        Left.func G a = some U ∧ x = iL.toFun ∘ a ∧
          T = Structure.imageSet iL.toFun U) ∨
      (∃ a : Fin (L.funcArity G) → F, ∃ U : Set F,
        Right.func G a = some U ∧ x = iR.toFun ∘ a ∧
          T = Structure.imageSet iR.toFun U) := by
  constructor
  · intro hValue
    rcases (hFree.defined_iff G x).mp ⟨T, hValue⟩ with
      ⟨a, ⟨U, hU⟩, hx⟩ | ⟨a, ⟨U, hU⟩, hx⟩
    · refine Or.inl ⟨a, U, hU, hx, ?_⟩
      have hTarget : Whole.func G x = some (Structure.imageSet iL.toFun U) := by
        rw [hx]
        simpa only [hU, Option.map_some] using (iL.map_func G a).symm
      exact Option.some.inj (hValue.symm.trans hTarget)
    · refine Or.inr ⟨a, U, hU, hx, ?_⟩
      have hTarget : Whole.func G x = some (Structure.imageSet iR.toFun U) := by
        rw [hx]
        simpa only [hU, Option.map_some] using (iR.map_func G a).symm
      exact Option.some.inj (hValue.symm.trans hTarget)
  · rintro (⟨a, U, hU, rfl, rfl⟩ | ⟨a, U, hU, rfl, rfl⟩)
    · simpa only [hU, Option.map_some] using (iL.map_func G a).symm
    · simpa only [hU, Option.map_some] using (iR.map_func G a).symm

/-- Every exact whole-value weak restriction of a full partial functional
free amalgam is again a full partial functional free amalgam of the exact
weak side and root restrictions.

The common weak root is not required to be closed in the ambient structure.
All four new maps are full embeddings between the weak structures; no source
projection is upgraded from an original-partial map to a full map. -/
theorem IsFreeAmalgam.wholeWeakInduce_withMaps
    {H E F C : Type v}
    {Root : PartialSetStructure L H}
    {Left : PartialSetStructure L E} {Right : PartialSetStructure L F}
    {Whole : PartialSetStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) :
    let Lset : Set E := iL.toFun ⁻¹' S
    let Rset : Set F := iR.toFun ⁻¹' S
    let Mset : Set H := (iL.toFun ∘ sL.toFun) ⁻¹' S
    ∃ (mL : Embedding (wholeWeakInduce Root Mset)
          (wholeWeakInduce Left Lset))
      (mR : Embedding (wholeWeakInduce Root Mset)
          (wholeWeakInduce Right Rset))
      (jL : Embedding (wholeWeakInduce Left Lset)
          (wholeWeakInduce Whole S))
      (jR : Embedding (wholeWeakInduce Right Rset)
          (wholeWeakInduce Whole S)),
      IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL.toFun a).1 = iL.toFun a.1) ∧
      (∀ b : Rset, (jR.toFun b).1 = iR.toFun b.1) := by
  classical
  dsimp only
  let Lset : Set E := iL.toFun ⁻¹' S
  let Rset : Set F := iR.toFun ⁻¹' S
  let Mset : Set H := (iL.toFun ∘ sL.toFun) ⁻¹' S
  have hOverlap (d : H) : iL.toFun (sL.toFun d) = iR.toFun (sR.toFun d) :=
    (hFree.overlap (sL.toFun d) (sR.toFun d)).mpr ⟨d, rfl, rfl⟩
  let mL : Embedding (wholeWeakInduce Root Mset)
      (wholeWeakInduce Left Lset) :=
    sL.wholeWeakRestrictExact Mset Lset (by intro x; rfl)
  let mR : Embedding (wholeWeakInduce Root Mset)
      (wholeWeakInduce Right Rset) :=
    sR.wholeWeakRestrictExact Mset Rset (by
      intro x
      change iL.toFun (sL.toFun x) ∈ S ↔ iR.toFun (sR.toFun x) ∈ S
      rw [hOverlap x])
  let jL : Embedding (wholeWeakInduce Left Lset)
      (wholeWeakInduce Whole S) :=
    iL.wholeWeakRestrictExact Lset S (by intro x; rfl)
  let jR : Embedding (wholeWeakInduce Right Rset)
      (wholeWeakInduce Whole S) :=
    iR.wholeWeakRestrictExact Rset S (by intro x; rfl)
  refine ⟨mL, mR, jL, jR, ?_, ?_, ?_⟩
  · constructor
    · intro z
      rcases hFree.covers z.1 with ⟨a, ha⟩ | ⟨b, hb⟩
      · have haS : a ∈ Lset := by
          change iL.toFun a ∈ S
          rw [← ha]
          exact z.2
        exact Or.inl ⟨⟨a, haS⟩, by
          apply Subtype.ext
          exact ha⟩
      · have hbS : b ∈ Rset := by
          change iR.toFun b ∈ S
          rw [← hb]
          exact z.2
        exact Or.inr ⟨⟨b, hbS⟩, by
          apply Subtype.ext
          exact hb⟩
    · intro a b
      constructor
      · intro hab
        have hraw : iL.toFun a.1 = iR.toFun b.1 := congrArg Subtype.val hab
        obtain ⟨d, had, hbd⟩ := (hFree.overlap a.1 b.1).mp hraw
        have hdS : d ∈ Mset := by
          change iL.toFun (sL.toFun d) ∈ S
          rw [← had]
          exact a.2
        refine ⟨(⟨d, hdS⟩ : Mset), ?_, ?_⟩
        · apply Subtype.ext
          exact had
        · apply Subtype.ext
          exact hbd
      · rintro ⟨d, had, hbd⟩
        have hleft : a.1 = sL.toFun d.1 := congrArg Subtype.val had
        have hright : b.1 = sR.toFun d.1 := congrArg Subtype.val hbd
        apply Subtype.ext
        change iL.toFun a.1 = iR.toFun b.1
        rw [hleft, hright]
        exact hOverlap d.1
    · intro R z
      constructor
      · intro hz
        have hzWhole : Whole.rel R (Subtype.val ∘ z) := hz
        rcases (hFree.rel_iff R (Subtype.val ∘ z)).mp hzWhole with
          ⟨x, hx, hzx⟩ | ⟨x, hx, hzx⟩
        · have hxS : ∀ i, x i ∈ Lset := by
            intro i
            change (iL.toFun ∘ x) i ∈ S
            rw [← congrFun hzx i]
            exact (z i).2
          let xs : Fin (L.relArity R) → Lset := fun i => ⟨x i, hxS i⟩
          refine Or.inl ⟨xs, hx, ?_⟩
          funext i
          apply Subtype.ext
          exact congrFun hzx i
        · have hxS : ∀ i, x i ∈ Rset := by
            intro i
            change (iR.toFun ∘ x) i ∈ S
            rw [← congrFun hzx i]
            exact (z i).2
          let xs : Fin (L.relArity R) → Rset := fun i => ⟨x i, hxS i⟩
          refine Or.inr ⟨xs, hx, ?_⟩
          funext i
          apply Subtype.ext
          exact congrFun hzx i
      · rintro (⟨xs, hx, rfl⟩ | ⟨xs, hx, rfl⟩)
        · exact (jL.map_rel_iff R xs).mpr hx
        · exact (jR.map_rel_iff R xs).mpr hx
    · intro G x
      constructor
      · intro hx
        have hxWhole : Whole.Defined G (Subtype.val ∘ x) :=
          wholeWeakInduce_defined_ambient Whole S G x hx
        rcases (hFree.defined_iff G (Subtype.val ∘ x)).mp hxWhole with
          ⟨a, _ha, hxa⟩ | ⟨a, _ha, hxa⟩
        · have haS : ∀ k, a k ∈ Lset := by
            intro k
            change (iL.toFun ∘ a) k ∈ S
            rw [← congrFun hxa k]
            exact (x k).2
          let as : Fin (L.funcArity G) → Lset := fun k => ⟨a k, haS k⟩
          have heq : x = jL.toFun ∘ as := by
            funext k
            apply Subtype.ext
            exact congrFun hxa k
          refine Or.inl ⟨as, ?_, heq⟩
          apply (jL.whole_defined_iff G as).mp
          rw [← heq]
          exact hx
        · have haS : ∀ k, a k ∈ Rset := by
            intro k
            change (iR.toFun ∘ a) k ∈ S
            rw [← congrFun hxa k]
            exact (x k).2
          let as : Fin (L.funcArity G) → Rset := fun k => ⟨a k, haS k⟩
          have heq : x = jR.toFun ∘ as := by
            funext k
            apply Subtype.ext
            exact congrFun hxa k
          refine Or.inr ⟨as, ?_, heq⟩
          apply (jR.whole_defined_iff G as).mp
          rw [← heq]
          exact hx
      · rintro (⟨as, ha, rfl⟩ | ⟨as, ha, rfl⟩)
        · exact (jL.whole_defined_iff G as).mpr ha
        · exact (jR.whole_defined_iff G as).mpr ha
  · intro a
    rfl
  · intro b
    rfl

end StructuralRamsey.PartialSetStructure
