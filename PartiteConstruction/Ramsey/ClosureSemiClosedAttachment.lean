import PartiteConstruction.Ramsey.ClosureSemiClosedRange
import PartiteConstruction.Ramsey.ClosureSemiClosedLines
import PartiteConstruction.Ramsey.ClosurePictureCoordinate
import PartiteConstruction.Iterated.AttachmentProjection

/-! # Closed core tests in the temporarily nonfunctional attachment

The core and old pieces are semi-closed, and every attaching-map range
is a relative U-substructure of the core. The support in the old piece
need NOT be relatively closed. The whole attachment may consequently
have multiple outputs above some roots and is not asserted semi-closed.

Nevertheless, any root that already has a closure tuple in the core has
that SAME unique tuple in the whole attachment. Thus every closed test
embedded entirely in the core remains relatively closed in the whole.
The final two results identify selected-profile copies by their actual
labels and instantiate this for the native Hales--Jewett line attachment.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}} {V W I X : Type v}
variable (Base : RelStructure L V) (S : Set V) (Core : RelStructure L W)
variable (maps : I → Embedding (Base.induce S) Core)

/-- Existing closure tuples still have valid prescribed roots, even
when different pieces give conflicting outputs above those roots. -/
theorem closureTuple_rootMatches
    {rules : ClosureDescription L}
    (hBase : IsUSemiClosed rules Base) (hCore : IsUSemiClosed rules Core)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → Vertex S (W := W) (I := I))
    (ht : (attach Base S Core maps).rel rule.symbol t) :
    rule.RootMatches (attach Base S Core maps) t := by
  rcases ht with ⟨a, ha, heq⟩ | ⟨i, a, ha, heq⟩
  · obtain ⟨r, hr⟩ := (hCore rule hrule).1 a ha
    refine ⟨(coreEmbedding Base S Core maps).comp r, ?_⟩
    intro k
    exact (congrFun heq (k.castLE rule.rootLE)).trans (congrArg Sum.inl (hr k))
  · obtain ⟨r, hr⟩ := (hBase rule hrule).1 a ha
    refine ⟨(copyEmbedding Base S Core maps i).comp r, ?_⟩
    intro k
    exact (congrFun heq (k.castLE rule.rootLE)).trans
      (congrArg (copyMap Base S Core maps i) (hr k))

/-- A core closure tuple prevents every competing output in the whole
attachment. Relative closedness is required only on the CORE side. -/
theorem closureTuple_eq_core_of_core_witness
    {rules : ClosureDescription L}
    (hBase : IsUSemiClosed rules Base) (hCore : IsUSemiClosed rules Core)
    (hMaps : ∀ i, IsUSubstructure rules Core (Set.range (maps i)))
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (t : Fin (L.arity rule.symbol) → Vertex S (W := W) (I := I))
    (ht : (attach Base S Core maps).rel rule.symbol t)
    (a : Fin (L.arity rule.symbol) → W) (ha : Core.rel rule.symbol a)
    (hRoot : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) = Sum.inl (a (k.castLE rule.rootLE))) :
    t = Sum.inl ∘ a := by
  classical
  rcases ht with ⟨b, hb, heq⟩ | ⟨i, b, hb, heq⟩
  · have hba : b = a := by
      apply (hCore rule hrule).2 b a hb ha
      intro k
      exact Sum.inl.inj ((congrFun heq (k.castLE rule.rootLE)).symm.trans (hRoot k))
    exact heq.trans (congrArg (fun z => Sum.inl ∘ z) hba)
  · have hbS (k : Fin rule.rootSize) : b (k.castLE rule.rootLE) ∈ S :=
      mem_of_copyMap_eq_inl
        ((congrFun heq (k.castLE rule.rootLE)).symm.trans (hRoot k))
    have hRootImage (k : Fin rule.rootSize) :
        maps i ⟨b (k.castLE rule.rootLE), hbS k⟩ = a (k.castLE rule.rootLE) := by
      apply Sum.inl.inj
      exact (copyMap_mem i (b (k.castLE rule.rootLE)) (hbS k)).symm.trans
        ((congrFun heq (k.castLE rule.rootLE)).symm.trans (hRoot k))
    have hImage : ∀ j : Fin (L.arity rule.symbol), a j ∈ Set.range (maps i) :=
      hMaps i rule hrule a ha (fun k => ⟨_, hRootImage k⟩)
    let c : Fin (L.arity rule.symbol) → S := fun j => Classical.choose (hImage j)
    have hc (j : Fin (L.arity rule.symbol)) : maps i (c j) = a j :=
      Classical.choose_spec (hImage j)
    have hcRel : Base.rel rule.symbol (Subtype.val ∘ c) := by
      apply ((maps i).map_rel_iff rule.symbol c).mp
      convert ha using 1
      funext j
      exact hc j
    have hbc : b = Subtype.val ∘ c := by
      apply (hBase rule hrule).2 _ _ hb hcRel
      intro k
      have hsub : (⟨b (k.castLE rule.rootLE), hbS k⟩ : S) = c (k.castLE rule.rootLE) :=
        (maps i).injective ((hRootImage k).trans (hc (k.castLE rule.rootLE)).symm)
      exact congrArg Subtype.val hsub
    funext j
    calc
      t j = copyMap Base S Core maps i (b j) := congrFun heq j
      _ = copyMap Base S Core maps i (c j).1 :=
        congrArg (copyMap Base S Core maps i) (congrFun hbc j)
      _ = Sum.inl (maps i (c j)) := copyMap_mem i (c j).1 (c j).2
      _ = Sum.inl (a j) := congrArg Sum.inl (hc j)

/-- A closed test embedded in the core stays relatively closed in the
whole attachment, even though that whole may fail semi-closedness. -/
theorem closed_core_test_range_isUSubstructure
    {rules : ClosureDescription L}
    (hBase : IsUSemiClosed rules Base) (hCore : IsUSemiClosed rules Core)
    (hMaps : ∀ i, IsUSubstructure rules Core (Set.range (maps i)))
    (Test : RelStructure L X) (hTest : IsUClosed rules Test)
    (e : Embedding Test Core) :
    IsUSubstructure rules (attach Base S Core maps)
      (Set.range ((coreEmbedding Base S Core maps).comp e)) := by
  classical
  let eO := (coreEmbedding Base S Core maps).comp e
  intro rule hrule t ht hRootRange j
  obtain ⟨r, hr⟩ := closureTuple_rootMatches Base S Core maps hBase hCore rule hrule t ht
  have hRange (k : Fin rule.rootSize) : ∃ x : X, r k = eO x := by
    obtain ⟨x, hx⟩ := hRootRange k
    exact ⟨x, (hr k).symm.trans hx.symm⟩
  let rT : Embedding rule.root Test := r.factorThroughRangeHeterogeneous eO hRange
  have hrT (k : Fin rule.rootSize) : r k = eO (rT k) :=
    Classical.choose_spec (hRange k)
  obtain ⟨a, ha, _⟩ := (hTest rule hrule).2 rT
  have hCoreTuple : Core.rel rule.symbol (e ∘ a) := (e.map_rel_iff rule.symbol a).mpr ha.1
  have hRoot : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) = Sum.inl ((e ∘ a) (k.castLE rule.rootLE)) := by
    intro k
    calc
      t (k.castLE rule.rootLE) = r k := hr k
      _ = eO (rT k) := hrT k
      _ = Sum.inl ((e ∘ a) (k.castLE rule.rootLE)) :=
        congrArg (fun x => Sum.inl (e x)) (ha.2 k).symm
  have hEq := closureTuple_eq_core_of_core_witness Base S Core maps
    hBase hCore hMaps rule hrule t ht (e ∘ a) hCoreTuple hRoot
  exact ⟨a j, (congrFun hEq j).symm⟩

/-- Selected labels force the test into the core; closedness then
makes its range a relative substructure of the whole little picture.
The old support is the EXACT inverse image of those labels. -/
theorem closed_profile_range_isUSubstructure
    {rules : ClosureDescription L} {P : Type v}
    (hBase : IsUSemiClosed rules Base) (hCore : IsUSemiClosed rules Core)
    (hMaps : ∀ i, IsUSubstructure rules Core (Set.range (maps i)))
    (p : V → P) (q : W → P) (J : Set P)
    (hSupport : ∀ x, x ∈ S ↔ p x ∈ J)
    (Test : RelStructure L X) (hTest : IsUClosed rules Test)
    (e : Embedding Test (attach Base S Core maps))
    (hProfile : ∀ x, fold q (fun _ : I => p) (e x) ∈ J) :
    IsUSubstructure rules (attach Base S Core maps) (Set.range e) := by
  classical
  let c := coreEmbedding Base S Core maps
  have hRange (x : X) : ∃ w : W, e x = c w := by
    cases hx : e x with
    | inl w => exact ⟨w, rfl⟩
    | inr z =>
        have hp : p z.2.1 ∈ J := by simpa only [hx, fold] using hProfile x
        exact False.elim (z.2.2 ((hSupport z.2.1).mpr hp))
  let g : Embedding Test Core := e.factorThroughRange c hRange
  have hEq : c.comp g = e := by
    apply Embedding.ext
    intro x
    exact (Classical.choose_spec (hRange x)).symm
  have h := closed_core_test_range_isUSubstructure Base S Core maps
    hBase hCore hMaps Test hTest g
  rw [hEq] at h
  exact h

end StructuralRamsey.RelStructure.Attachment

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree
universe u v
variable {L : RelLanguage.{u}} {P Q V I X : Type v} {N : ℕ}

/-- Actual native line attachment: ALL closed selected-profile copies
are relative U-substructures. No closed control, closed support, or
semi-closed whole attachment is assumed. This is the input for the
recursive relative-copy theorem after naming the parts. -/
theorem closed_profile_in_native_line_attachment
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hOld : IsUClosed rules Old.toRelStructure) (hN : 0 < N)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (Test : RelStructure L X) (hTest : IsUClosed rules Test)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (hProfile : ∀ x, RelStructure.Attachment.fold
      (fun z : Vertex (Old.restrict alpha) N => alpha z.part)
      (fun _ : I => Old.part) (e x) ∈ Set.range alpha) :
    IsUSubstructure rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) (Set.range e) := by
  have hR : IsUSemiClosed rules (Old.restrict alpha).toRelStructure :=
    hOld.induce_isUSemiClosed (Old.support alpha)
  apply RelStructure.Attachment.closed_profile_range_isUSubstructure
    Old.toRelStructure (Old.support alpha)
    (power (Old.restrict alpha) N).toRelStructure
    (closureLineMaps Old alpha A hRestricted lines)
    hOld.isUSemiClosed (power_isUSemiClosed (Old.restrict alpha) hR hN)
    (fun i => line_range_isUSubstructure_of_semiClosed
      (Old.restrict alpha) hRestricted hR (lines i))
    Old.part (fun z => alpha z.part) (Set.range alpha) (fun _ => Iff.rfl)
    Test hTest e hProfile

end StructuralRamsey.Partite.Induced
