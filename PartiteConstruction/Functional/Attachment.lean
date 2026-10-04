import PartiteConstruction.Functional.Operations
import PartiteConstruction.Structure.Attachment

/-! # Free attachment for functional partite systems

This is the full relation/function analogue of Partite.Attachment.
The overlap is closed, so the structural core/copy maps are full embeddings.
The part map is inherited from the core and copies, and relation/function
transversality is preserved.
-/
namespace StructuralRamsey.FunctionalPartite.Attachment

open Structure

universe u v
variable {L : Language.{u}} {P V W I : Type v}
variable (B : System L P V) (S : Set V)
variable (hS : B.toStructure.IsClosed S)
variable (D : System L P W)
variable (f : I → Embedding (B.induce S hS) D)

abbrev Vertex := Structure.Attachment.Vertex S (W := W) (I := I)

def part : Vertex S (W := W) (I := I) → P :=
  Sum.elim D.part (fun ix => B.part ix.2.1)

@[simp] theorem part_copyMap (i : I) (x : V) :
    part B S D
      (Structure.Attachment.copyMap B.toStructure S hS D.toStructure
        (fun i => (f i).toEmbedding) i x) = B.part x := by
  classical
  by_cases hx : x ∈ S
  · simpa [Structure.Attachment.copyMap, hx, part, System.induce]
      using (f i).map_part ⟨x, hx⟩
  · simp [Structure.Attachment.copyMap, hx, part]

noncomputable def attach :
    System L P (Vertex S (W := W) (I := I)) where
  toStructure :=
    Structure.Attachment.attach B.toStructure S hS D.toStructure
      (fun i => (f i).toEmbedding)
  part := part B S D
  relTransversal := by
    intro R x hx k l hkl
    change
      (Structure.Attachment.attach B.toStructure S hS D.toStructure
        (fun i => (f i).toEmbedding)).rel R x at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨i, y, hy, rfl⟩
    · exact congrArg Sum.inl (D.relTransversal R y hy k l hkl)
    · simp only [Function.comp_apply, part_copyMap] at hkl
      exact congrArg
        (Structure.Attachment.copyMap B.toStructure S hS D.toStructure
          (fun j => (f j).toEmbedding) i)
        (B.relTransversal R y hy k l hkl)
  funcTransversal := by
    classical
    intro F x y z hy hz hp
    let maps :
        I → Structure.Embedding (B.toStructure.induce S hS) D.toStructure :=
      fun i => (f i).toEmbedding
    by_cases hcore : ∀ k, ∃ a : W, x k = Sum.inl a
    · choose a ha using hcore
      have hargs : x = Sum.inl ∘ a := by
        funext k
        exact ha k
      have hy' :
          y ∈
            (Structure.Attachment.attach
              B.toStructure S hS D.toStructure maps).func F
              (Sum.inl ∘ a) := by
        rw [← hargs]
        exact hy
      have hz' :
          z ∈
            (Structure.Attachment.attach
              B.toStructure S hS D.toStructure maps).func F
              (Sum.inl ∘ a) := by
        rw [← hargs]
        exact hz
      rw [← Structure.Attachment.core_func
        (B := B.toStructure) (S := S) (hS := hS)
        (D := D.toStructure) (f := maps) F a] at hy' hz'
      rcases hy' with ⟨yy, hyy, hyout⟩
      rcases hz' with ⟨zz, hzz, hzout⟩
      have hpD : D.part yy = D.part zz := by
        have hp' := hp
        rw [← hyout, ← hzout] at hp'
        exact hp'
      have heq := D.funcTransversal F a yy zz hyy hzz hpD
      calc
        y = Sum.inl yy := hyout.symm
        _ = Sum.inl zz := congrArg Sum.inl heq
        _ = z := hzout
    · push Not at hcore
      obtain ⟨k, hk⟩ := hcore
      cases hxk : x k with
      | inl a =>
          exact (hk a hxk).elim
      | inr p =>
          let i : I := p.1
          let outside := p.2
          have getCopy :
              ∀ {t : Vertex S (W := W) (I := I)},
                t ∈
                    (Structure.Attachment.attach
                      B.toStructure S hS D.toStructure maps).func F x →
                ∃ args : Fin (L.funcArity F) → V, ∃ out : V,
                  out ∈ B.func F args ∧
                  x =
                    Structure.Attachment.copyMap
                      B.toStructure S hS D.toStructure maps i ∘ args ∧
                  t =
                    Structure.Attachment.copyMap
                      B.toStructure S hS D.toStructure maps i out := by
            intro t ht
            rcases ht with
              ⟨a, b, hb, hxa, htb⟩ |
              ⟨j, args, out, hout, hxargs, htout⟩
            · have hk0 := congrFun hxa k
              rw [hxk] at hk0
              simp at hk0
            · have hnot : args k ∉ S := by
                intro hmem
                have hk0 := congrFun hxargs k
                have hk1 :
                    Sum.inr p =
                      Structure.Attachment.copyMap
                        B.toStructure S hS D.toStructure
                        (fun q => (f q).toEmbedding) j (args k) := by
                  simpa [maps, Function.comp_apply] using hk0
                rw [Structure.Attachment.copyMap_mem
                    (B := B.toStructure) (S := S) (hS := hS)
                    (D := D.toStructure)
                    (f := fun q => (f q).toEmbedding)
                    j (args k) hmem] at hk1
                simp at hk1
              have hji : j = i := by
                have hk0 := congrFun hxargs k
                have hk1 :
                    Sum.inr p =
                      Structure.Attachment.copyMap
                        B.toStructure S hS D.toStructure
                        (fun q => (f q).toEmbedding) j (args k) := by
                  simpa [maps, Function.comp_apply] using hk0
                rw [Structure.Attachment.copyMap_not_mem
                    (B := B.toStructure) (S := S) (hS := hS)
                    (D := D.toStructure)
                    (f := fun q => (f q).toEmbedding)
                    j (args k) hnot] at hk1
                exact congrArg Prod.fst (Sum.inr.inj hk1.symm)
              subst j
              exact ⟨args, out, hout, hxargs, htout⟩
          obtain ⟨ay, byv, hry, hargsY, houtY⟩ := getCopy hy
          obtain ⟨az, bz, hrz, hargsZ, houtZ⟩ := getCopy hz
          have hargsEq : ay = az := by
            funext j
            apply Structure.Attachment.copyMap_injective
              (B := B.toStructure) (S := S) (hS := hS)
              (D := D.toStructure) (f := maps) i
            have hj := congrFun (hargsY.symm.trans hargsZ) j
            simpa [Function.comp_apply] using hj
          subst az
          have hpB : B.part byv = B.part bz := by
            have hp' := hp
            rw [houtY, houtZ] at hp'
            have hp'' :
                part B S D
                    (Structure.Attachment.copyMap
                      B.toStructure S hS D.toStructure
                      (fun q => (f q).toEmbedding) i byv) =
                  part B S D
                    (Structure.Attachment.copyMap
                      B.toStructure S hS D.toStructure
                      (fun q => (f q).toEmbedding) i bz) := by
              simpa [maps] using hp'
            exact
              (part_copyMap B S hS D f i byv).symm.trans
                (hp''.trans (part_copyMap B S hS D f i bz))
          have houtEq := B.funcTransversal F ay byv bz hry hrz hpB
          calc
            y =
                Structure.Attachment.copyMap
                  B.toStructure S hS D.toStructure maps i byv := houtY
            _ =
                Structure.Attachment.copyMap
                  B.toStructure S hS D.toStructure maps i bz :=
              congrArg
                (Structure.Attachment.copyMap
                  B.toStructure S hS D.toStructure maps i) houtEq
            _ = z := houtZ.symm

noncomputable def coreEmbedding :
    Embedding D (attach B S hS D f) where
  toEmbedding :=
    Structure.Attachment.coreEmbedding
      B.toStructure S hS D.toStructure
      (fun i => (f i).toEmbedding)
  map_part _ := rfl

noncomputable def copyEmbedding (i : I) :
    Embedding B (attach B S hS D f) where
  toEmbedding :=
    Structure.Attachment.copyEmbedding
      B.toStructure S hS D.toStructure
      (fun j => (f j).toEmbedding) i
  map_part := part_copyMap B S hS D f i

theorem copy_extends (i : I) (x : S) :
    copyEmbedding B S hS D f i x.1 =
      coreEmbedding B S hS D f (f i x) :=
  Structure.Attachment.copy_extends
    B.toStructure S hS D.toStructure
    (fun j => (f j).toEmbedding) i x

end StructuralRamsey.FunctionalPartite.Attachment
