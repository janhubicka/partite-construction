import PartiteConstruction.Functional.Closed
import PartiteConstruction.Partite.Attachment

/-! # U-closed free attachment

If the overlap is closed for the encoded function relations and each attaching
map is U-closed, then the core and every attached copy are U-closed in the
free attachment. Under U-transversality of the pieces, the attachment remains
U-transversal.
-/
namespace StructuralRamsey.Partite.Closed.Attachment

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V W I : Type v}
variable (B : Partite.System L.graph P V) (S : Set V)
variable (D : Partite.System L.graph P W)
variable (f : I → Partite.Closed.Embedding (B.induce S) D)

abbrev Vertex (S : Set V) (W I : Type v) :=
  Partite.Attachment.Vertex S (W := W) (I := I)

noncomputable def attach : Partite.System L.graph P (Vertex S W I) :=
  Partite.Attachment.attach B S D (fun i => (f i).1)

variable {B S D f}

/-- If the overlap is U-closed, the core inclusion is U-closed. -/
theorem core_closed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S) :
    RelStructure.FunctionClosedMap
      D.toRelStructure
      (attach B S D f).toRelStructure
      (Partite.Attachment.coreEmbedding
        B S D (fun i => (f i).1)) := by
  classical
  intro F x y hy
  change
    (Partite.Attachment.attach B S D (fun i => (f i).1)).rel
      (.inr F)
      (Structure.funcTuple
        ((Partite.Attachment.coreEmbedding
          B S D (fun i => (f i).1)) ∘ x) y) at hy
  let g := fun i => (f i).1.toEmbedding
  change
    (RelStructure.Attachment.attach
      B.toRelStructure S D.toRelStructure g).rel
      (.inr F)
      (Structure.funcTuple (Sum.inl ∘ x) y) at hy
  rcases hy with hcore | hcopy
  · rcases hcore with ⟨a, ha, heq⟩
    have hargs : a = x := by
      funext j
      have hj := congrFun heq (Fin.castSucc j)
      exact Sum.inl.inj (by
        simpa [Structure.funcTuple, Function.comp_apply] using hj)
    subst a
    have hout := congrFun heq (Fin.last (L.funcArity F))
    refine ⟨?_, ha, ?_⟩
    · exact y
    · exact Sum.inl.inj (by
        simpa [Structure.funcTuple, Function.comp_apply] using hout).symm
  · rcases hcopy with ⟨i, a, ha, heq⟩
    have haS : ∀ j : Fin (L.funcArity F), a (Fin.castSucc j) ∈ S := by
      intro j
      apply RelStructure.Attachment.mem_of_copyMap_eq_inl
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g)
      have hj := congrFun heq (Fin.castSucc j)
      simpa [Structure.funcTuple, Function.comp_apply] using hj.symm
    let args : Fin (L.funcArity F) → V :=
      fun j => a (Fin.castSucc j)
    let out : V := a (Fin.last (L.funcArity F))
    have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
      convert ha using 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rfl
      · rfl
    have houtS : out ∈ S := hS F args out hrel haS
    let argsS : Fin (L.funcArity F) → S :=
      fun j => ⟨args j, haS j⟩
    let outS : S := ⟨out, houtS⟩
    have hDrel :
        D.rel (.inr F)
          (Structure.funcTuple
            ((f i) ∘ argsS) ((f i) outS)) := by
      have hsRel :
          (B.induce S).rel (.inr F)
            (Structure.funcTuple argsS outS) := by
        exact hrel
      have ht :=
        ((f i).1.toEmbedding.map_rel_iff
          (.inr F) (Structure.funcTuple argsS outS)).mpr hsRel
      have htuple :
          (f i).1 ∘ Structure.funcTuple argsS outS =
            Structure.funcTuple ((f i) ∘ argsS) ((f i) outS) := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [Structure.funcTuple, Function.comp_apply]
        · simp [Structure.funcTuple, Function.comp_apply]
      rw [← htuple]
      exact ht
    have hargsD : (f i) ∘ argsS = x := by
      funext j
      have hj := congrFun heq (Fin.castSucc j)
      apply Sum.inl.inj
      simpa [argsS, args, Structure.funcTuple, Function.comp_apply,
        RelStructure.Attachment.copyMap_mem (f := g) i (args j) (haS j)]
        using hj
    rw [hargsD] at hDrel
    have houtEq :
        y = Sum.inl ((f i) outS) := by
      have hj := congrFun heq (Fin.last (L.funcArity F))
      simpa [outS, out, Structure.funcTuple, Function.comp_apply,
        RelStructure.Attachment.copyMap_mem (f := g) i out houtS]
        using hj.symm
    refine ⟨(f i) outS, hDrel, ?_⟩
    exact houtEq.symm

/-- If the overlap is U-closed and the attaching maps are U-closed, each
attached-copy inclusion is U-closed. -/
theorem copy_closed
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (i : I) :
    RelStructure.FunctionClosedMap
      B.toRelStructure
      (attach B S D f).toRelStructure
      (Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i) := by
  classical
  intro F x y hy
  let g := fun j => (f j).1.toEmbedding
  let cm := RelStructure.Attachment.copyMap
    B.toRelStructure S D.toRelStructure g i
  change
    (RelStructure.Attachment.attach
      B.toRelStructure S D.toRelStructure g).rel
      (.inr F)
      (Structure.funcTuple (cm ∘ x) y) at hy
  rcases hy with hcore | hcopy
  · rcases hcore with ⟨a, ha, heq⟩
    have hxS : ∀ j : Fin (L.funcArity F), x j ∈ S := by
      intro j
      apply RelStructure.Attachment.mem_of_copyMap_eq_inl
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g)
      have hj := congrFun heq (Fin.castSucc j)
      simpa [cm, Structure.funcTuple, Function.comp_apply] using hj
    let xs : Fin (L.funcArity F) → S := fun j => ⟨x j, hxS j⟩
    have hargs : (f i) ∘ xs = a := by
      funext j
      exact Sum.inl.inj (by
        have hj := congrFun heq (Fin.castSucc j)
        simpa [cm, xs, Structure.funcTuple, Function.comp_apply,
          RelStructure.Attachment.copyMap_mem (f := g) i (x j) (hxS j)]
          using hj)
    have hyD : y ∈ Set.range Sum.inl := by
      let b := a (Fin.last (L.funcArity F))
      exact ⟨b, by
        have hj := congrFun heq (Fin.last (L.funcArity F))
        simpa [Structure.funcTuple, Function.comp_apply] using hj.symm⟩
    rcases hyD with ⟨yD, rfl⟩
    have hDrel : D.rel (.inr F)
        (Structure.funcTuple ((f i) ∘ xs) yD) := by
      have htuple :
          Structure.funcTuple ((f i) ∘ xs) yD = a := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · rfl
        · exact congrFun hargs k
      rw [htuple]
      exact ha
    obtain ⟨z, hz, hzy⟩ :=
      (f i).2 F xs yD hDrel
    refine ⟨z.1, ?_, ?_⟩
    · exact hz
    · have hzS : z.1 ∈ S := z.2
      change cm z.1 = Sum.inl yD
      rw [RelStructure.Attachment.copyMap_mem
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) i z.1 hzS]
      exact congrArg Sum.inl hzy
  · rcases hcopy with ⟨j, a, ha, heq⟩
    by_cases hxS : ∀ k : Fin (L.funcArity F), x k ∈ S
    · have haS : ∀ k : Fin (L.funcArity F), a (Fin.castSucc k) ∈ S := by
        intro k
        apply RelStructure.Attachment.mem_of_copyMap_eq_inl
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) (i := j)
        have hk := congrFun heq (Fin.castSucc k)
        exact hk.symm.trans
          (RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i (x k) (hxS k))
      let args : Fin (L.funcArity F) → V :=
        fun k => a (Fin.castSucc k)
      let out : V := a (Fin.last (L.funcArity F))
      have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
        convert ha using 1
        funext k
        refine Fin.lastCases ?_ (fun q => ?_) k <;> rfl
      have houtS : out ∈ S := hS F args out hrel haS
      let argsS : Fin (L.funcArity F) → S :=
        fun k => ⟨args k, haS k⟩
      let outS : S := ⟨out, houtS⟩
      have hjRel :
          D.rel (.inr F)
            (Structure.funcTuple ((f j) ∘ argsS) ((f j) outS)) := by
        have hsRel :
            (B.induce S).rel (.inr F)
              (Structure.funcTuple argsS outS) := hrel
        have ht :=
          ((f j).1.toEmbedding.map_rel_iff
            (.inr F) (Structure.funcTuple argsS outS)).mpr hsRel
        have htuple :
            (f j).1 ∘ Structure.funcTuple argsS outS =
              Structure.funcTuple ((f j) ∘ argsS) ((f j) outS) := by
          funext k
          refine Fin.lastCases ?_ (fun q => ?_) k
          · simp [Structure.funcTuple, Function.comp_apply]
          · simp [Structure.funcTuple, Function.comp_apply]
        rw [← htuple]
        exact ht
      let xs : Fin (L.funcArity F) → S := fun k => ⟨x k, hxS k⟩
      have hargsEq : (f i) ∘ xs = (f j) ∘ argsS := by
        funext k
        apply Sum.inl.inj
        have hk := congrFun heq (Fin.castSucc k)
        simpa [cm, xs, argsS, args, Structure.funcTuple,
          Function.comp_apply,
          RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i (x k) (hxS k),
          RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) j (args k) (haS k)] using hk
      rw [← hargsEq] at hjRel
      obtain ⟨z, hz, hzy⟩ :=
        (f i).2 F xs ((f j) outS) hjRel
      refine ⟨z.1, hz, ?_⟩
      have hzS : z.1 ∈ S := z.2
      have houtEq : y =
          Sum.inl ((f j) outS) := by
        have hk := congrFun heq (Fin.last (L.funcArity F))
        simpa [outS, out, Structure.funcTuple, Function.comp_apply,
          RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) j out houtS] using hk.symm
      change cm z.1 = y
      rw [houtEq,
        RelStructure.Attachment.copyMap_mem
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) i z.1 hzS]
      exact congrArg Sum.inl hzy
    · push Not at hxS
      obtain ⟨k, hk⟩ := hxS
      have hij :=
        RelStructure.Attachment.index_eq_of_outside
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) hk (by
            have hcoord := congrFun heq (Fin.castSucc k)
            simpa [cm, Structure.funcTuple, Function.comp_apply] using hcoord)
      subst j
      let out := a (Fin.last (L.funcArity F))
      refine ⟨out, ?_, ?_⟩
      · have hrel : B.rel (.inr F) (Structure.funcTuple x out) := by
          have hargs : x = fun q => a (Fin.castSucc q) := by
            funext q
            apply RelStructure.Attachment.copyMap_injective
              (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
              (f := g) i
            have hcoord := congrFun heq (Fin.castSucc q)
            simpa [cm, Structure.funcTuple, Function.comp_apply] using hcoord
          convert ha using 1
          funext q
          refine Fin.lastCases ?_ (fun r => ?_) q
          · rfl
          · exact (congrFun hargs r).symm
        exact hrel
      · have hout := congrFun heq (Fin.last (L.funcArity F))
        simpa [cm, out, Structure.funcTuple, Function.comp_apply] using hout.symm

/-- Closed free attachment preserves U-transversality. -/
theorem uTransversal
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hB : B.FunctionOutputTransversal)
    (hD : D.FunctionOutputTransversal) :
    (attach B S D f).FunctionOutputTransversal := by
  classical
  intro F x y z hy hz hp
  let g := fun i => (f i).1.toEmbedding
  let R := (RelStructure.Attachment.attach
    B.toRelStructure S D.toRelStructure g)
  change R.rel (.inr F) (Structure.funcTuple x y) at hy
  change R.rel (.inr F) (Structure.funcTuple x z) at hz
  by_cases hcoreArgs : ∀ k : Fin (L.funcArity F), ∃ a : W, x k = .inl a
  · choose a ha using hcoreArgs
    have hcoreOutput :
        ∀ {t : Vertex S W I},
          R.rel (.inr F) (Structure.funcTuple x t) →
          ∃ b : W, t = .inl b := by
      intro t ht
      rcases ht with hcore | hcopy
      · rcases hcore with ⟨q, hq, heq⟩
        refine ⟨q (Fin.last (L.funcArity F)), ?_⟩
        have hout := congrFun heq (Fin.last (L.funcArity F))
        simpa [Structure.funcTuple, Function.comp_apply] using hout.symm
      · rcases hcopy with ⟨i, q, hq, heq⟩
        have hqS : ∀ k : Fin (L.funcArity F),
            q (Fin.castSucc k) ∈ S := by
          intro k
          apply RelStructure.Attachment.mem_of_copyMap_eq_inl
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g)
          have hk := congrFun heq (Fin.castSucc k)
          rw [ha k] at hk
          simpa [Structure.funcTuple, Function.comp_apply] using hk.symm
        let args : Fin (L.funcArity F) → V :=
          fun k => q (Fin.castSucc k)
        let out : V := q (Fin.last (L.funcArity F))
        have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
          convert hq using 1
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j <;> rfl
        have houtS : out ∈ S := hS F args out hrel hqS
        refine ⟨(f i) ⟨out, houtS⟩, ?_⟩
        have houtEq := congrFun heq (Fin.last (L.funcArity F))
        simpa [out, Structure.funcTuple, Function.comp_apply,
          RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i out houtS] using houtEq.symm
    obtain ⟨yy, hyy⟩ := hcoreOutput hy
    obtain ⟨zz, hzz⟩ := hcoreOutput hz
    subst y
    subst z
    have hargsD :
        ∀ k, x k = Sum.inl (a k) := ha
    have hyD : D.rel (.inr F)
        (Structure.funcTuple a yy) := by
      exact (RelStructure.Attachment.core_rel_iff
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) (.inr F) (Structure.funcTuple a yy)).mp (by
          convert hy using 1
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · rfl
          · simp [Structure.funcTuple, hargsD])
    have hzD : D.rel (.inr F)
        (Structure.funcTuple a zz) := by
      exact (RelStructure.Attachment.core_rel_iff
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) (.inr F) (Structure.funcTuple a zz)).mp (by
          convert hz using 1
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · rfl
          · simp [Structure.funcTuple, hargsD])
    have hpD : D.part yy = D.part zz := by
      simpa [Partite.Attachment.part] using hp
    exact congrArg Sum.inl (hD F a yy zz hyD hzD hpD)
  · push Not at hcoreArgs
    obtain ⟨k, hk⟩ := hcoreArgs
    cases hx : x k with
    | inl a => exact (hk a hx).elim
    | inr ix =>
        let i := ix.1
        let outx := ix.2
        have getCopy :
            ∀ {t : Vertex S W I},
              R.rel (.inr F) (Structure.funcTuple x t) →
              ∃ q : Fin (L.funcArity F) → V, ∃ b : V,
                B.rel (.inr F) (Structure.funcTuple q b) ∧
                x = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i ∘ q ∧
                t = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i b := by
          intro t ht
          have htupleOutside :
              (Structure.funcTuple x t) (Fin.castSucc k) =
                .inr (i, outx) := by
            simp [Structure.funcTuple, hx, i, outx]
          obtain ⟨qall, hq, heq⟩ :=
            RelStructure.Attachment.relation_eq_copy_of_contains_outside
              (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
              (f := g) ht (Fin.castSucc k) i outx htupleOutside
          let q : Fin (L.funcArity F) → V :=
            fun j => qall (Fin.castSucc j)
          let b : V := qall (Fin.last (L.funcArity F))
          have hrel : B.rel (.inr F) (Structure.funcTuple q b) := by
            convert hq using 1
            funext j
            refine Fin.lastCases ?_ (fun r => ?_) j <;> rfl
          have hargs :
              x = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i ∘ q := by
            funext j
            have hj := congrFun heq (Fin.castSucc j)
            simpa [q, Structure.funcTuple, Function.comp_apply] using hj
          have hout :
              t = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i b := by
            have hj := congrFun heq (Fin.last (L.funcArity F))
            simpa [b, Structure.funcTuple, Function.comp_apply] using hj
          exact ⟨q, b, hrel, hargs, hout⟩
        obtain ⟨qy, byv, hry, hargsY, houtY⟩ := getCopy hy
        obtain ⟨qz, bz, hrz, hargsZ, houtZ⟩ := getCopy hz
        have hq : qy = qz := by
          funext j
          apply RelStructure.Attachment.copyMap_injective
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i
          have := congrFun (hargsY.trans hargsZ.symm) j
          simpa [Function.comp_apply] using this
        subst qz
        have hpB : B.part byv = B.part bz := by
          simpa [houtY, houtZ, Partite.Attachment.part_copyMap] using hp
        have hbybz := hB F qy byv bz hry hrz hpB
        subst bz
        exact houtY.trans houtZ.symm

end StructuralRamsey.Partite.Closed.Attachment
