import PartiteConstruction.Functional.ClosedPartite
import PartiteConstruction.Partite.Attachment

/-! # U-closed free attachment

If the overlap is U-closed and every attaching map is U-closed, then the core
and every attached copy are U-closed in the relational free attachment.
Moreover U-transversality is preserved. The proof uses only the dichotomy:
all function inputs lie in the core, or one input lies outside and therefore
determines the unique attached copy containing the entire graph tuple.
-/
namespace StructuralRamsey.Partite.Closed.Attachment

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V W I : Type v}
variable (B : Partite.System L.graph P V) (S : Set V)
variable (D : Partite.System L.graph P W)

abbrev Vertex (S : Set V) (W I : Type v) :=
  Partite.Attachment.Vertex S (W := W) (I := I)

noncomputable def attach
    (f : I → Partite.Closed.Embedding (B.induce S) D) :
    Partite.System L.graph P (Vertex S W I) :=
  Partite.Attachment.attach B S D (fun i => (f i).1)

variable {B S D}
variable {f : I → Partite.Closed.Embedding (B.induce S) D}

private abbrev relMaps :=
  fun i => (f i).1.toEmbedding

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
  let g := relMaps (f := f)
  let core : W → Vertex S W I := fun d => Sum.inl d
  change
    (RelStructure.Attachment.attach
      B.toRelStructure S D.toRelStructure g).rel
      (.inr F) (Structure.funcTuple (core ∘ x) y) at hy
  cases y with
  | inl d =>
      have hcore :
          (RelStructure.Attachment.attach
            B.toRelStructure S D.toRelStructure g).rel
            (.inr F) (core ∘ Structure.funcTuple x d) := by
        rw [Structure.comp_funcTuple]
        exact hy
      have hd :
          D.rel (.inr F) (Structure.funcTuple x d) := by
        exact (RelStructure.Attachment.core_rel_iff
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) (.inr F) (Structure.funcTuple x d)).mp hcore
      exact ⟨d, hd, rfl⟩
  | inr p =>
      let j := p.1
      let out0 := p.2
      have hk :
          (Structure.funcTuple (core ∘ x) (Sum.inr p))
              (Fin.last (L.funcArity F)) =
            Sum.inr (j, out0) := by rfl
      obtain ⟨q, hq, heq⟩ :=
        RelStructure.Attachment.relation_eq_copy_of_contains_outside
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) hy (Fin.last (L.funcArity F)) j out0 hk
      let args : Fin (L.funcArity F) → V :=
        fun k => q (Fin.castSucc k)
      let out : V := q (Fin.last (L.funcArity F))
      have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
        have heta : Structure.funcTuple args out = q := by
          simpa [args, out, Language.graph] using
            (Structure.funcTuple_eta (t := q))
        rw [heta]
        exact hq
      have hargsS : ∀ k, args k ∈ S := by
        intro k
        apply RelStructure.Attachment.mem_of_copyMap_eq_inl
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g)
        have h := congrFun heq (Fin.castSucc k)
        have h' :
            core (x k) =
              RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g j (args k) := by
          simpa [core, args, Structure.funcTuple, Function.comp_apply] using h
        exact h'.symm
      have houtS : out ∈ S := hS F args out hrel hargsS
      have hout := congrFun heq (Fin.last (L.funcArity F))
      have hout' :
          Sum.inr (j, out0) =
            RelStructure.Attachment.copyMap
              B.toRelStructure S D.toRelStructure g j out := by
        simpa [out, Structure.funcTuple, Function.comp_apply] using hout
      rw [RelStructure.Attachment.copyMap_mem
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) j out houtS] at hout'
      exact (Sum.noConfusion hout')

/-- If the overlap is U-closed and the attaching maps are U-closed, every
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
  let g := relMaps (f := f)
  let cm : V → Vertex S W I :=
    RelStructure.Attachment.copyMap
      B.toRelStructure S D.toRelStructure g i
  let core : W → Vertex S W I := fun d => Sum.inl d
  change
    (RelStructure.Attachment.attach
      B.toRelStructure S D.toRelStructure g).rel
      (.inr F) (Structure.funcTuple (cm ∘ x) y) at hy
  by_cases hxS : ∀ k, x k ∈ S
  · let xs : Fin (L.funcArity F) → S :=
      fun k => ⟨x k, hxS k⟩
    have hinput :
        cm ∘ x = core ∘ ((f i) ∘ xs) := by
      funext k
      change
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure g i (x k) =
          Sum.inl ((f i) ⟨x k, hxS k⟩)
      exact RelStructure.Attachment.copyMap_mem
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) i (x k) (hxS k)
    have hyCore :
        (RelStructure.Attachment.attach
          B.toRelStructure S D.toRelStructure g).rel
          (.inr F)
          (Structure.funcTuple
            (core ∘ ((f i) ∘ xs)) y) := by
      rw [← hinput]
      exact hy
    obtain ⟨d, hd, hdy⟩ :=
      core_closed (B := B) (S := S) (D := D) (f := f) hS
        F ((f i) ∘ xs) y hyCore
    obtain ⟨z, hz, hzd⟩ := (f i).2 F xs d hd
    have hzB :
        B.rel (.inr F) (Structure.funcTuple x z.1) := by
      change
        B.rel (.inr F)
          (Subtype.val ∘ Structure.funcTuple xs z) at hz
      have htuple :
          Subtype.val ∘ Structure.funcTuple xs z =
            Structure.funcTuple x z.1 := by
        funext q
        refine Fin.lastCases ?_ (fun k => ?_) q
        · rfl
        · rfl
      rw [htuple] at hz
      exact hz
    refine ⟨z.1, hzB, ?_⟩
    calc
      cm z.1 = core ((f i) z) := by
        change
          RelStructure.Attachment.copyMap
            B.toRelStructure S D.toRelStructure g i z.1 =
            Sum.inl ((f i) z)
        exact RelStructure.Attachment.copyMap_mem
          (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
          (f := g) i z.1 z.2
      _ = core d := congrArg core hzd
      _ = y := hdy
  · push Not at hxS
    obtain ⟨k, hkS⟩ := hxS
    let outside : {x : V // x ∉ S} := ⟨x k, hkS⟩
    have hk :
        (Structure.funcTuple (cm ∘ x) y) (Fin.castSucc k) =
          Sum.inr (i, outside) := by
      change cm (x k) = Sum.inr (i, outside)
      exact RelStructure.Attachment.copyMap_not_mem
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) i (x k) hkS
    obtain ⟨q, hq, heq⟩ :=
      RelStructure.Attachment.relation_eq_copy_of_contains_outside
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) hy (Fin.castSucc k) i outside hk
    let args : Fin (L.funcArity F) → V :=
      fun j => q (Fin.castSucc j)
    let out : V := q (Fin.last (L.funcArity F))
    have hargs : x = args := by
      funext j
      apply RelStructure.Attachment.copyMap_injective
        (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
        (f := g) i
      have hj := congrFun heq (Fin.castSucc j)
      change cm (x j) =
        RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure g i (args j)
      simpa [cm, args, Structure.funcTuple, Function.comp_apply] using hj
    have hrel : B.rel (.inr F) (Structure.funcTuple x out) := by
      have heta : Structure.funcTuple args out = q := by
        simpa [args, out, Language.graph] using
          (Structure.funcTuple_eta (t := q))
      rw [hargs, heta]
      exact hq
    refine ⟨out, hrel, ?_⟩
    have hout := congrFun heq (Fin.last (L.funcArity F))
    change y =
      RelStructure.Attachment.copyMap
        B.toRelStructure S D.toRelStructure g i out at hout
    exact hout.symm

/-- Closed free attachment preserves U-transversality. -/
theorem uTransversal
    (hS : RelStructure.FunctionClosedSet B.toRelStructure S)
    (hB : B.FunctionOutputTransversal)
    (hD : D.FunctionOutputTransversal) :
    (attach B S D f).FunctionOutputTransversal := by
  classical
  intro F x y z hy hz hp
  let g := relMaps (f := f)
  by_cases hcore : ∀ k, ∃ a : W, x k = Sum.inl a
  · choose a ha using hcore
    have hargs :
        x = Sum.inl ∘ a := by
      funext k
      exact ha k
    have hy' :
        (RelStructure.Attachment.attach
          B.toRelStructure S D.toRelStructure g).rel
          (.inr F)
          (Structure.funcTuple (Sum.inl ∘ a) y) := by
      rw [← hargs]
      exact hy
    have hz' :
        (RelStructure.Attachment.attach
          B.toRelStructure S D.toRelStructure g).rel
          (.inr F)
          (Structure.funcTuple (Sum.inl ∘ a) z) := by
      rw [← hargs]
      exact hz
    obtain ⟨yy, hyy, hyout⟩ :=
      core_closed (B := B) (S := S) (D := D) (f := f) hS
        F a y hy'
    obtain ⟨zz, hzz, hzout⟩ :=
      core_closed (B := B) (S := S) (D := D) (f := f) hS
        F a z hz'
    have hpD : D.part yy = D.part zz := by
      have hp' := hp
      change
        (attach B S D f).part y =
          (attach B S D f).part z at hp'
      rw [← hyout, ← hzout] at hp'
      exact hp'
    have heq := hD F a yy zz hyy hzz hpD
    calc
      y = Sum.inl yy := hyout.symm
      _ = Sum.inl zz := congrArg Sum.inl heq
      _ = z := hzout
  · push Not at hcore
    obtain ⟨k, hk⟩ := hcore
    cases hx : x k with
    | inl a => exact (hk a hx).elim
    | inr p =>
        let i := p.1
        let outside := p.2
        have getCopy :
            ∀ {t : Vertex S W I},
              (RelStructure.Attachment.attach
                B.toRelStructure S D.toRelStructure g).rel
                (.inr F) (Structure.funcTuple x t) →
              ∃ args : Fin (L.funcArity F) → V, ∃ out : V,
                B.rel (.inr F) (Structure.funcTuple args out) ∧
                x = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i ∘ args ∧
                t = RelStructure.Attachment.copyMap
                    B.toRelStructure S D.toRelStructure g i out := by
          intro t ht
          have hk' :
              (Structure.funcTuple x t) (Fin.castSucc k) =
                Sum.inr (i, outside) := by
            simpa [i, outside, Structure.funcTuple] using hx
          obtain ⟨q, hq, heq⟩ :=
            RelStructure.Attachment.relation_eq_copy_of_contains_outside
              (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
              (f := g) ht (Fin.castSucc k) i outside hk'
          let args : Fin (L.funcArity F) → V :=
            fun j => q (Fin.castSucc j)
          let out : V := q (Fin.last (L.funcArity F))
          have hrel : B.rel (.inr F) (Structure.funcTuple args out) := by
            have heta : Structure.funcTuple args out = q := by
              simpa [args, out, Language.graph] using
                (Structure.funcTuple_eta (t := q))
            rw [heta]
            exact hq
          have hargs :
              x = RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i ∘ args := by
            funext j
            have hj := congrFun heq (Fin.castSucc j)
            simpa [args, Structure.funcTuple, Function.comp_apply] using hj
          have hout :
              t = RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i out := by
            have hj := congrFun heq (Fin.last (L.funcArity F))
            simpa [out, Structure.funcTuple, Function.comp_apply] using hj
          exact ⟨args, out, hrel, hargs, hout⟩
        obtain ⟨ay, byv, hry, hargsY, houtY⟩ := getCopy hy
        obtain ⟨az, bz, hrz, hargsZ, houtZ⟩ := getCopy hz
        have hargsEq : ay = az := by
          funext j
          apply RelStructure.Attachment.copyMap_injective
            (B := B.toRelStructure) (S := S) (D := D.toRelStructure)
            (f := g) i
          have hj := congrFun (hargsY.trans hargsZ.symm) j
          simpa [Function.comp_apply] using hj
        subst az
        have hpB : B.part byv = B.part bz := by
          have hp' := hp
          rw [houtY, houtZ] at hp'
          simpa [Partite.Attachment.part_copyMap] using hp'
        have houtEq := hB F ay byv bz hry hrz hpB
        calc
          y = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i byv := houtY
          _ = RelStructure.Attachment.copyMap
                B.toRelStructure S D.toRelStructure g i bz :=
              congrArg
                (RelStructure.Attachment.copyMap
                  B.toRelStructure S D.toRelStructure g i) houtEq
          _ = z := houtZ.symm

end StructuralRamsey.Partite.Closed.Attachment
