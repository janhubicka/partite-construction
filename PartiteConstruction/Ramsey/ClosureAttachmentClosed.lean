import PartiteConstruction.Ramsey.ClosureRootCover
import PartiteConstruction.Ramsey.ClosureAttachmentFold

/-! # Closedness of the native simultaneous attachment

The old structure and core are U-closed and the attaching support is a
relative U-substructure of the old structure. These hypotheses suffice
for U-closedness of the existing Attachment.attach, for any index family.

Relative closedness of the core and copy ranges is proved FIRST, without
assuming whole-attachment closedness. Ordinary irreducibility of each
prescribed root localises it in a piece. The closed-root-cover criterion
then gives both existence and uniqueness of closure tuples.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}} {V W I : Type v}
variable (Old : RelStructure L V) (S : Set V) (Core : RelStructure L W)
variable (maps : I → Embedding (Old.induce S) Core)

/-- A core vertex belongs to a copy exactly when it belongs to that
copy's attaching-map range. No closure assumption is needed. -/
theorem core_mem_copy_range_iff (i : I) (w : W) :
    (Sum.inl w : Vertex S (W := W) (I := I)) ∈
      Set.range (copyEmbedding Old S Core maps i) ↔
    w ∈ Set.range (maps i) := by
  constructor
  · rintro ⟨x, hx⟩
    have hxS : x ∈ S := mem_of_copyMap_eq_inl hx
    refine ⟨⟨x, hxS⟩, ?_⟩
    apply Sum.inl.inj
    exact (copyMap_mem i x hxS).symm.trans hx
  · rintro ⟨x, hx⟩
    exact ⟨x.1, (copyMap_mem i x.1 x.2).trans (congrArg Sum.inl hx)⟩

/-- Relative closedness of the attaching support prevents a closure
tuple rooted in the core from acquiring an exterior output. -/
theorem core_range_isUSubstructure
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Old S) :
    IsUSubstructure rules (attach Old S Core maps)
      (Set.range (coreEmbedding Old S Core maps)) := by
  intro rule hrule t ht hRoot j
  rcases ht with ⟨xs, _, heq⟩ | ⟨i, xs, hxs, heq⟩
  · exact ⟨xs j, (congrFun heq j).symm⟩
  · have hInput : ∀ k : Fin rule.rootSize,
        xs (k.castLE rule.rootLE) ∈ S := by
      intro k
      obtain ⟨w, hw⟩ := hRoot k
      apply mem_of_copyMap_eq_inl (B := Old) (D := Core) (f := maps)
      exact (congrFun heq (k.castLE rule.rootLE)).symm.trans hw.symm
    have hOutput : xs j ∈ S := hS rule hrule xs hxs hInput j
    exact ⟨maps i ⟨xs j, hOutput⟩,
      ((congrFun heq j).trans (copyMap_mem i (xs j) hOutput)).symm⟩

/-- Each copy range is relatively closed before whole-attachment
closedness is known. Competing core tuples are controlled by closedness
of the attaching-map range INSIDE the already closed core. -/
theorem copy_range_isUSubstructure
    {rules : ClosureDescription L}
    (hOld : IsUClosed rules Old) (hCore : IsUClosed rules Core)
    (hS : IsUSubstructure rules Old S) (i : I) :
    IsUSubstructure rules (attach Old S Core maps)
      (Set.range (copyEmbedding Old S Core maps i)) := by
  classical
  have hSupport := hOld.induce_of_USubstructure S hS
  have hMapRange : IsUSubstructure rules Core (Set.range (maps i)) :=
    (maps i).range_isUSubstructure hSupport hCore
  intro rule hrule t ht hRoot j
  by_cases hInputCore : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) ∈ Set.range (coreEmbedding Old S Core maps)
  · have hAllCore : ∀ k : Fin (L.arity rule.symbol),
        t k ∈ Set.range (coreEmbedding Old S Core maps) :=
      core_range_isUSubstructure Old S Core maps hS rule hrule t ht hInputCore
    let xs : Fin (L.arity rule.symbol) → W :=
      fun k => Classical.choose (hAllCore k)
    have hxs (k : Fin (L.arity rule.symbol)) :
        (Sum.inl (xs k) : Vertex S (W := W) (I := I)) = t k :=
      Classical.choose_spec (hAllCore k)
    have hEq : Sum.inl ∘ xs = t := funext hxs
    have hRel : Core.rel rule.symbol xs := by
      apply (core_rel_iff (B := Old) (S := S) (D := Core) (f := maps)
        rule.symbol xs).mp
      rw [hEq]
      exact ht
    have hRootMap : ∀ k : Fin rule.rootSize,
        xs (k.castLE rule.rootLE) ∈ Set.range (maps i) := by
      intro k
      apply (core_mem_copy_range_iff Old S Core maps i _).mp
      rw [hxs]
      exact hRoot k
    obtain ⟨a, ha⟩ := hMapRange rule hrule xs hRel hRootMap j
    refine ⟨a.1, ?_⟩
    calc
      copyEmbedding Old S Core maps i a.1 = Sum.inl (maps i a) :=
        copyMap_mem i a.1 a.2
      _ = Sum.inl (xs j) := congrArg Sum.inl ha
      _ = t j := hxs j
  · push Not at hInputCore
    obtain ⟨k, hk⟩ := hInputCore
    obtain ⟨a, ha⟩ := hRoot k
    have haNot : a ∉ S := by
      intro haS
      apply hk
      exact ⟨maps i ⟨a, haS⟩, (copyMap_mem i a haS).symm.trans ha⟩
    have hOutside : t (k.castLE rule.rootLE) = Sum.inr (i, ⟨a, haNot⟩) :=
      ha.symm.trans (copyMap_not_mem i a haNot)
    obtain ⟨xs, _, heq⟩ := relation_eq_copy_of_contains_outside
      ht (k.castLE rule.rootLE) i ⟨a, haNot⟩ hOutside
    exact ⟨xs j, (congrFun heq j).symm⟩

/-- The native simultaneous attachment is U-closed. There is no
whole-closedness premise, no finite-index assumption, and no extra
irreducibility requirement on Old, Core, or the attaching support. -/
theorem attach_isUClosed
    {rules : ClosureDescription L}
    (hOld : IsUClosed rules Old) (hCore : IsUClosed rules Core)
    (hS : IsUSubstructure rules Old S) :
    IsUClosed rules (attach Old S Core maps) := by
  classical
  let Carrier : Option I → Type v
    | none => W
    | some _ => V
  let Piece : ∀ i : Option I, RelStructure L (Carrier i)
    | none => Core
    | some _ => Old
  let inc : ∀ i : Option I, Embedding (Piece i) (attach Old S Core maps)
    | none => coreEmbedding Old S Core maps
    | some i => copyEmbedding Old S Core maps i
  apply isUClosed_of_closed_root_cover rules (attach Old S Core maps) Piece inc
  · intro i
    cases i with
    | none => exact hCore
    | some i => exact hOld
  · intro i
    cases i with
    | none => exact core_range_isUSubstructure Old S Core maps hS
    | some i => exact copy_range_isUSubstructure Old S Core maps hOld hCore hS i
  · intro rule hrule t ht
    rcases ht with ⟨xs, hxs, heq⟩ | ⟨i, xs, hxs, heq⟩
    · exact ⟨none, xs, hxs, heq⟩
    · exact ⟨some i, xs, hxs, heq⟩
  · intro rule hrule e
    have hSeed : ((attach Old S Core maps).induce (Set.range e)).Irreducible :=
      rule.rootIrreducible.range_embedding e
    rcases irreducible_core_or_copy (Set.range e) hSeed with hInCore | ⟨i, hInCopy⟩
    · have hRange (k : Fin rule.rootSize) :
          ∃ w, e k = coreEmbedding Old S Core maps w :=
        hInCore ⟨e k, ⟨k, rfl⟩⟩
      exact ⟨none,
        e.factorThroughRangeHeterogeneous (coreEmbedding Old S Core maps) hRange,
        fun k => (Classical.choose_spec (hRange k)).symm⟩
    · have hRange (k : Fin rule.rootSize) :
          ∃ x, e k = copyEmbedding Old S Core maps i x :=
        hInCopy ⟨e k, ⟨k, rfl⟩⟩
      exact ⟨some i,
        e.factorThroughRangeHeterogeneous (copyEmbedding Old S Core maps i) hRange,
        fun k => (Classical.choose_spec (hRange k)).symm⟩

end StructuralRamsey.RelStructure.Attachment
