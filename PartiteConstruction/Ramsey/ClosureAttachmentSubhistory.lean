import PartiteConstruction.Ramsey.ClosureAttachmentFold
import PartiteConstruction.Ramsey.ClosureProjectedGenerators
import PartiteConstruction.Ramsey.ClosureEmbeddedSourceClosed
import PartiteConstruction.Relational.AttachmentReindex

/-! # Extracting the subfamily needed by a generated Picture test

Closing a generating set cannot introduce a new exterior copy index:
the complement of each individual exterior is a relative U-substructure.
Thus the WHOLE tested structure embeds in the subattachment consisting
of the core and the copies already met by its generators.

This is an exact induced embedding on the original test. No test vertex
or weak image is added. The larger subattachment used as a completion
ambient retains the core and the selected entire old copies. It is closed
whenever the full attachment is closed and its attaching support is
relatively closed in the old picture.
-/

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}} {V W I X : Type v}
variable (Old : RelStructure L V) (S : Set V) (Core : RelStructure L W)
variable (maps : I → Embedding (Old.induce S) Core)

/-- Selecting copy indices keeps the whole core and gives an induced
embedding into the original multi-attachment. -/
noncomputable def subfamilyEmbedding (J : Set I) :
    Embedding (attach Old S Core (fun i : J => maps i.1))
      (attach Old S Core maps) :=
  reindexEmbedding (fun i : J => maps i.1) maps
    ⟨Subtype.val, Subtype.val_injective⟩ (fun _ => rfl)

/-- The selected subfamily is relatively closed: a tuple from an omitted
copy rooted in the selected family must be rooted entirely in the core. -/
theorem subfamily_range_isUSubstructure
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Old S) (J : Set I) :
    IsUSubstructure rules (attach Old S Core maps)
      (Set.range (subfamilyEmbedding Old S Core maps J)) := by
  classical
  let emb := subfamilyEmbedding Old S Core maps J
  intro rule hrule t ht hRoot l
  rcases ht with ⟨xs, _, heq⟩ | ⟨i, xs, hxs, heq⟩
  · exact ⟨Sum.inl (xs l), (congrFun heq l).symm⟩
  · by_cases hi : i ∈ J
    · let iJ : J := ⟨i, hi⟩
      refine ⟨copyMap Old S Core (fun k : J => maps k.1) iJ (xs l), ?_⟩
      calc
        emb (copyMap Old S Core (fun k : J => maps k.1) iJ (xs l)) =
            copyMap Old S Core maps i (xs l) :=
          reindexVertex_copy (fun k : J => maps k.1) maps
            ⟨Subtype.val, Subtype.val_injective⟩ (fun _ => rfl) iJ (xs l)
        _ = t l := (congrFun heq l).symm
    · have hInput : ∀ k : Fin rule.rootSize,
          xs (k.castLE rule.rootLE) ∈ S := by
        intro k
        by_contra hNot
        obtain ⟨y, hy⟩ := hRoot k
        have hbad : emb y = Sum.inr (i, ⟨xs (k.castLE rule.rootLE), hNot⟩) :=
          hy.trans ((congrFun heq (k.castLE rule.rootLE)).trans
            (copyMap_not_mem i (xs (k.castLE rule.rootLE)) hNot))
        cases y with
        | inl w => cases hbad
        | inr pair =>
          have hIndex : pair.1.1 = i := congrArg Prod.fst (Sum.inr.inj hbad)
          apply hi
          rw [← hIndex]
          exact pair.1.2
      have hOut : xs l ∈ S := hS rule hrule xs hxs hInput l
      exact ⟨Sum.inl (maps i ⟨xs l, hOut⟩),
        ((congrFun heq l).trans (copyMap_mem i (xs l) hOut)).symm⟩

/-- Any selected subattachment is intrinsically closed if the whole is
closed. No independent closedness certificate for each selected family
is required. -/
theorem subfamily_isUClosed
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Old S)
    (hWhole : IsUClosed rules (attach Old S Core maps)) (J : Set I) :
    IsUClosed rules (attach Old S Core (fun i : J => maps i.1)) :=
  (subfamilyEmbedding Old S Core maps J).source_isUClosed_of_range_USubstructure
    hWhole (subfamily_range_isUSubstructure Old S Core maps hS J)

/-- Every exterior index reached by a generated test is reached already
by one of its generators. The tested structure need not be closed. -/
theorem exterior_index_from_generator
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Old S)
    (Test : RelStructure L X)
    (e : Embedding Test (attach Old S Core maps))
    (G : Set X) (hGen : IsUGenerating rules Test G)
    (i : I) (x : X) (hx : OutsideAt (W := W) (I := I) S i (e x)) :
    ∃ g ∈ G, OutsideAt (W := W) (I := I) S i (e g) := by
  classical
  by_contra hNo
  let R : Set X := {y | ¬ OutsideAt (W := W) (I := I) S i (e y)}
  have hR : IsUSubstructure rules Test R :=
    (rest_isUSubstructure Old S Core maps hS i).preimage_embedding e
  have hGR : G ⊆ R := by
    intro g hg hout
    exact hNo ⟨g, hg, hout⟩
  have hHull := UClosureHull_minimal rules Test hR hGR
  have hxHull : x ∈ UClosureHull rules Test G := by
    rw [hGen]
    trivial
  exact hHull hxHull hx

/-- Exact test factorisation through the selected subhistory. It is
sufficient that the selected indices include generator exterior indices;
all other tested vertices follow by closure, without a new vertex bound. -/
theorem factor_through_generator_subfamily
    {rules : ClosureDescription L}
    (hS : IsUSubstructure rules Old S)
    (Test : RelStructure L X)
    (e : Embedding Test (attach Old S Core maps))
    (G : Set X) (hGen : IsUGenerating rules Test G)
    (J : Set I)
    (hSelected : ∀ g ∈ G, ∀ i,
      OutsideAt (W := W) (I := I) S i (e g) → i ∈ J) :
    ∃ d : Embedding Test (attach Old S Core (fun i : J => maps i.1)),
      ∀ x, subfamilyEmbedding Old S Core maps J (d x) = e x := by
  classical
  let emb := subfamilyEmbedding Old S Core maps J
  have hRange (x : X) : ∃ y, e x = emb y := by
    cases hVal : e x with
    | inl w => exact ⟨Sum.inl w, hVal⟩
    | inr pair =>
      have hOut : OutsideAt (W := W) (I := I) S pair.1 (e x) :=
        ⟨pair.2, hVal⟩
      obtain ⟨g, hg, hgOut⟩ := exterior_index_from_generator
        Old S Core maps hS Test e G hGen pair.1 x hOut
      have hi : pair.1 ∈ J := hSelected g hg pair.1 hgOut
      exact ⟨Sum.inr (⟨pair.1, hi⟩, pair.2), hVal⟩
  exact ⟨e.factorThroughRange emb hRange,
    fun x => (Classical.choose_spec (hRange x)).symm⟩

end StructuralRamsey.RelStructure.Attachment
