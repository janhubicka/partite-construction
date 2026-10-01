import PartiteConstruction.Partite.Induced
import PartiteConstruction.Partite.Attachment

/-! # The induced projection invariant under free attachment

An irreducible substructure of a free attachment lies in the core or in one
attached copy. Hence a homomorphism-embedding projection on the pieces glues
to a homomorphism-embedding projection on the attachment.
-/
namespace StructuralRamsey.Partite.Attachment

open RelStructure

universe u v w z t
variable {L : RelLanguage.{u}} {P : Type v} {V : Type w} {W : Type z} {I : Type t}
variable {A : RelStructure L P}
variable (B : System L P V) (S : Set V) (D : System L P W)
variable (f : I → Embedding (B.induce S) D)

/-- Free attachment preserves the induced-construction projection invariant. -/
theorem attach_isPartiteOver
    (hB : B.IsPartiteOver A) (hD : D.IsPartiteOver A) :
    (attach B S D f).IsPartiteOver A := by
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R x hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨i, y, hy, rfl⟩
    · exact hD.1 R y hy
    · have hA := hB.1 R y hy
      convert hA using 1
      funext k
      exact part_copyMap B S D f i (y k)
  · intro T hT
    exact (attach B S D f).part_injOn_irreducible T hT
  · intro T hT R x hxT hA
    have hsplit :=
      RelStructure.Attachment.irreducible_core_or_copy
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := fun i => (f i).toEmbedding) T hT
    rcases hsplit with hcore | ⟨i, hcopy⟩
    · let pre : T → W := fun s => Classical.choose (hcore s)
      have hpre (s : T) : s.1 = Sum.inl (pre s) :=
        Classical.choose_spec (hcore s)
      let U : Set W := Set.range pre
      have hU : (D.toRelStructure.induce U).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R', z, k, l, hz, hzk, hzl⟩ := hT hsab
        change (attach B S D f).rel R' (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R') → W := fun q => pre (z q)
        have heq : Subtype.val ∘ z = Sum.inl ∘ y := by
          funext q
          exact hpre (z q)
        have hDrel : D.rel R' y := by
          rw [heq] at hz
          exact (RelStructure.Attachment.core_rel_iff
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := fun i => (f i).toEmbedding) R' y).mp hz
        let yU : Fin (L.arity R') → U :=
          fun q => ⟨y q, ⟨z q, rfl⟩⟩
        refine ⟨R', yU, k, l, ?_, ?_, ?_⟩
        · exact hDrel
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      let xs : Fin (L.arity R) → T := fun k => ⟨x k, hxT k⟩
      let y : Fin (L.arity R) → W := fun k => pre (xs k)
      have hyU : ∀ k, y k ∈ U := fun k => ⟨xs k, rfl⟩
      have hApart : A.rel R (D.part ∘ y) := by
        convert hA using 1
        funext k
        change D.part (pre ⟨x k, hxT k⟩) = part B S D (x k)
        have hk := hpre ⟨x k, hxT k⟩
        calc
          D.part (pre ⟨x k, hxT k⟩) =
              part B S D (Sum.inl (pre ⟨x k, hxT k⟩)) := rfl
          _ = part B S D (x k) := (congrArg (part B S D) hk).symm
      have hDrel := hD.reflect_rel_on U hU R y hyU hApart
      have heq : x = Sum.inl ∘ y := by
        funext k
        exact hpre (xs k)
      rw [heq]
      exact Or.inl ⟨y, hDrel, rfl⟩
    · let pre : T → V := fun s => Classical.choose (hcopy s)
      have hpre (s : T) : s.1 =
          RelStructure.Attachment.copyMap B.toRelStructure S D.toRelStructure
            (fun i => (f i).toEmbedding) i (pre s) :=
        Classical.choose_spec (hcopy s)
      let U : Set V := Set.range pre
      have hU : (B.toRelStructure.induce U).Irreducible := by
        intro a b hab
        rcases a.property with ⟨sa, hsa⟩
        rcases b.property with ⟨sb, hsb⟩
        have hsab : sa ≠ sb := by
          intro hs
          apply hab
          apply Subtype.ext
          rw [← hsa, ← hsb, hs]
        obtain ⟨R', z, k, l, hz, hzk, hzl⟩ := hT hsab
        change (attach B S D f).rel R' (Subtype.val ∘ z) at hz
        let y : Fin (L.arity R') → V := fun q => pre (z q)
        have heq :
            Subtype.val ∘ z =
              RelStructure.Attachment.copyMap B.toRelStructure S D.toRelStructure
                (fun j => (f j).toEmbedding) i ∘ y := by
          funext q
          exact hpre (z q)
        have hBrel : B.rel R' y := by
          rw [heq] at hz
          exact (RelStructure.Attachment.copy_rel_iff
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := fun j => (f j).toEmbedding) i R' y).mp hz
        let yU : Fin (L.arity R') → U :=
          fun q => ⟨y q, ⟨z q, rfl⟩⟩
        refine ⟨R', yU, k, l, ?_, ?_, ?_⟩
        · exact hBrel
        · apply Subtype.ext
          change pre (z k) = a.1
          rw [hzk]
          exact hsa
        · apply Subtype.ext
          change pre (z l) = b.1
          rw [hzl]
          exact hsb
      let xs : Fin (L.arity R) → T := fun k => ⟨x k, hxT k⟩
      let y : Fin (L.arity R) → V := fun k => pre (xs k)
      have hyU : ∀ k, y k ∈ U := fun k => ⟨xs k, rfl⟩
      have hApart : A.rel R (B.part ∘ y) := by
        convert hA using 1
        funext k
        change B.part (pre ⟨x k, hxT k⟩) = part B S D (x k)
        have hk := hpre ⟨x k, hxT k⟩
        exact (part_copyMap B S D f i (pre ⟨x k, hxT k⟩)).symm.trans
          (congrArg (part B S D) hk).symm
      have hBrel := hB.reflect_rel_on U hU R y hyU hApart
      have heq :
          x = RelStructure.Attachment.copyMap B.toRelStructure S D.toRelStructure
            (fun j => (f j).toEmbedding) i ∘ y := by
        funext k
        exact hpre (xs k)
      rw [heq]
      exact Or.inr ⟨i, y, hBrel, rfl⟩

end StructuralRamsey.Partite.Attachment
