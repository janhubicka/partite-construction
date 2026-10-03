import PartiteConstruction.Iterated.IndexedTarget
import PartiteConstruction.Relational.Attachment

/-! # One fixed-support attachment: geometric uniform witness

This file isolates the geometric part of the uniform final-sparsening repair.
For a multi-copy attachment with one fixed irreducible support in the base,
a finite set of selected copy indices is enough provided it contains

* every copy contributing an outside vertex to the tested set; and
* a representative for the trace on the tested set of every ambient
  control-copy living in an attached base copy.

If the core test together with all selected roots fits inside the available
local-tree budget, then the attached structure has a full controlled
local-tree witness on the tested set.

The finite counting/representative-selection lemma is deliberately separated
from this theorem.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W I : Type v}
variable {Control : RelStructure L UA}
variable {Base : RelStructure L VB}
variable {Core : RelStructure L W}
variable {S : Set VB}
variable {f : I → Embedding (Base.induce S) Core}

/-- A controlled local-tree witness for one tested set in a simultaneous
attachment over a fixed irreducible support. -/
theorem attachmentWitness_of_selected
    [Finite UA] [Finite VB] [Finite W] [Fintype I]
    (hControl : Control.Irreducible)
    (hRoot : (Base.induce S).Irreducible)
    (m : ℕ)
    (hCore : LocallyTreeLike Control Base Core m)
    (Test : Finset (Attachment.Vertex S (W := W) (I := I)))
    (J : Finset I)
    (R : Finset W)
    (hRcard : R.card ≤ m)
    (hCoreTest :
      ∀ w : W, (Sum.inl w : Attachment.Vertex S (W := W) (I := I)) ∈ Test →
        w ∈ R)
    (hRoots :
      ∀ j : I, j ∈ J → ∀ x : ↥S, f j x ∈ R)
    (hActive :
      ∀ i : I, ∀ x : {x : VB // x ∉ S},
        (Sum.inr (i, x) : Attachment.Vertex S (W := W) (I := I)) ∈ Test →
          i ∈ J)
    (hTrace :
      ∀ α : Embedding Control (Attachment.attach Base S Core f),
        (∃ i : I, ∀ a : UA, ∃ b : VB,
          α a = Attachment.copyMap Base S Core f i b) →
        ∃ j : I, j ∈ J ∧
          ∃ β : Embedding Control Base,
            ∀ a : UA, α a ∈ Test →
              α a = Attachment.copyMap Base S Core f j (β a)) :
    ∃ (Y : Type v) (T : RelStructure L Y),
      TreeAmalgam Base Y T ∧
      ∃ q : ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))) → Y,
        ((Attachment.attach Base S Core f).induce
          (↑Test : Set (Attachment.Vertex S (W := W) (I := I)))).
          IsHomomorphismEmbedding T q ∧
        ∀ α : Embedding Control (Attachment.attach Base S Core f),
          ∃ α' : Embedding Control T,
            ∀ a : UA, ∀ ha : α a ∈ Test,
              ∃ a' : UA, q ⟨α a, ha⟩ = α' a' := by
  classical
  obtain ⟨Y₀, T₀, hTree₀, g, hg, hctrl⟩ := hCore R hRcard

  let rootR (j : I) (hj : j ∈ J) :
      Embedding (Base.induce S) (Core.induce (↑R : Set W)) := {
    toFun := fun x => ⟨f j x, hRoots j hj x⟩
    injective := by
      intro x y hxy
      apply f j |>.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro Rel x
      change Core.rel Rel (f j ∘ (Subtype.val ∘ x)) ↔
        Base.rel Rel (Subtype.val ∘ x)
      exact (f j).map_rel_iff Rel (Subtype.val ∘ x)
  }

  rcases hTree₀.exists_base_embedding with ⟨base₀⟩
  let fallback : Embedding (Base.induce S) T₀ :=
    base₀.comp (inclusion Base S)
  let rootTarget : I → Embedding (Base.induce S) T₀ := fun j =>
    if hj : j ∈ J then
      Classical.choose (hg.after_irreducible_embedding hRoot (rootR j hj))
    else
      fallback
  have hrootTarget (j : I) (hj : j ∈ J) (x : ↥S) :
      rootTarget j x = g (rootR j hj x) := by
    simp only [rootTarget, dif_pos hj]
    exact Classical.choose_spec
      (hg.after_irreducible_embedding hRoot (rootR j hj)) x

  obtain ⟨Y, T, hTree, coreT, copies, hcopies⟩ :=
    TreeAmalgam.attachIndexed hRoot hTree₀ rootTarget

  let q :
      ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))) → Y :=
    fun z =>
      match hz : z.1 with
      | .inl w =>
          coreT (g ⟨w, hCoreTest w (by simpa [hz] using z.2)⟩)
      | .inr ix =>
          copies ix.1 ix.2.1

  have q_inl (w : W)
      (hw : (Sum.inl w : Attachment.Vertex S (W := W) (I := I)) ∈ Test) :
      q ⟨Sum.inl w, hw⟩ =
        coreT (g ⟨w, hCoreTest w hw⟩) := by
    simp [q]

  have q_inr (i : I) (x : {x : VB // x ∉ S})
      (hx : (Sum.inr (i, x) : Attachment.Vertex S (W := W) (I := I)) ∈ Test) :
      q ⟨Sum.inr (i, x), hx⟩ = copies i x.1 := by
    simp [q]

  have q_copy (j : I) (hj : j ∈ J) (b : VB)
      (hbT : Attachment.copyMap Base S Core f j b ∈ Test) :
      q ⟨Attachment.copyMap Base S Core f j b, hbT⟩ =
        copies j b := by
    by_cases hb : b ∈ S
    · let x : ↥S := ⟨b, hb⟩
      have hmem :
          (Sum.inl (f j x) :
            Attachment.Vertex S (W := W) (I := I)) ∈ Test := by
        simpa [Attachment.copyMap_mem j b hb] using hbT
      calc
        q ⟨Attachment.copyMap Base S Core f j b, hbT⟩ =
            coreT (g ⟨f j x, hRoots j hj x⟩) := by
              simpa [Attachment.copyMap_mem j b hb, x] using
                q_inl (f j x) hmem
        _ = coreT (rootTarget j x) := by
              exact congrArg coreT (hrootTarget j hj x).symm
        _ = copies j b := by
              exact (hcopies j x).symm
    · let x : {x : VB // x ∉ S} := ⟨b, hb⟩
      have hmem :
          (Sum.inr (j, x) :
            Attachment.Vertex S (W := W) (I := I)) ∈ Test := by
        simpa [Attachment.copyMap_not_mem j b hb, x] using hbT
      simpa [Attachment.copyMap_not_mem j b hb, x] using q_inr j x hmem

  have mapCore
      (Rel : L.Symbol)
      (z : Fin (L.arity Rel) →
        ↥(↑Test : Set (Attachment.Vertex S (W := W) (I := I))))
      (y : Fin (L.arity Rel) → W)
      (hy : Core.rel Rel y)
      (hzy : ∀ k, (z k).1 = Sum.inl (y k)) :
      T.rel Rel (q ∘ z) := by
    let yR : Fin (L.arity Rel) → ↥(↑R : Set W) :=
      fun k => ⟨y k, hCoreTest (y k) (by
        have hk := (z k).2
        rw [hzy k] at hk
        exact hk)⟩
    have hyR :
        (Core.induce (↑R : Set W)).rel Rel yR := by
      change Core.rel Rel (Subtype.val ∘ yR)
      convert hy using 1
      funext k
      rfl
    have hgRel : T₀.rel Rel (g ∘ yR) := hg.map_rel hyR
    have hcoreRel : T.rel Rel (coreT ∘ (g ∘ yR)) :=
      (coreT.map_rel_iff Rel (g ∘ yR)).mpr hgRel
    convert hcoreRel using 1
    funext k
    change q (z k) = coreT (g (yR k))
    rw [hzy k]
    simpa [yR] using q_inl (y k) (by
      have hk := (z k).2
      rw [hzy k] at hk
      exact hk)

  have hq :
      ((Attachment.attach Base S Core f).induce
          (↑Test : Set (Attachment.Vertex S (W := W) (I := I)))).
        IsHomomorphismEmbedding T q := by
    constructor
    · intro Rel z hz
      change
        (Attachment.attach Base S Core f).rel Rel
          (Subtype.val ∘ z) at hz
      rcases hz with ⟨y, hy, hzy⟩ | ⟨i, x, hx, hzx⟩
      · apply mapCore Rel z y hy
        intro k
        exact congrFun hzy k
      · by_cases hall : ∀ k, x k ∈ S
        · let xs : Fin (L.arity Rel) → ↥S :=
            fun k => ⟨x k, hall k⟩
          have hroot :
              (Base.induce S).rel Rel xs := by
            change Base.rel Rel (Subtype.val ∘ xs)
            convert hx using 1
            funext k
            rfl
          have hcore : Core.rel Rel (f i ∘ xs) :=
            ((f i).map_rel_iff Rel xs).mpr hroot
          apply mapCore Rel z (f i ∘ xs) hcore
          intro k
          have hk := congrFun hzx k
          change (z k).1 =
            Attachment.copyMap Base S Core f i (x k) at hk
          rw [Attachment.copyMap_mem i (x k) (hall k)] at hk
          exact hk
        · push Not at hall
          obtain ⟨k₀, hk₀⟩ := hall
          have hz₀ := congrFun hzx k₀
          change (z k₀).1 =
            Attachment.copyMap Base S Core f i (x k₀) at hz₀
          have hout :
              (z k₀).1 =
                Sum.inr (i, (⟨x k₀, hk₀⟩ :
                  {x : VB // x ∉ S})) := by
            simpa [Attachment.copyMap_not_mem i (x k₀) hk₀] using hz₀
          have hiJ : i ∈ J := by
            apply hActive i ⟨x k₀, hk₀⟩
            have hm := (z k₀).2
            rw [hout] at hm
            exact hm
          have hcopyRel : T.rel Rel (copies i ∘ x) :=
            (copies i).map_rel_iff Rel x |>.mpr hx
          convert hcopyRel using 1
          funext k
          change q (z k) = copies i (x k)
          have hk := congrFun hzx k
          change (z k).1 =
            Attachment.copyMap Base S Core f i (x k) at hk
          have hmem :
              Attachment.copyMap Base S Core f i (x k) ∈ Test := by
            rw [← hk]
            exact (z k).2
          calc
            q (z k) =
                q ⟨Attachment.copyMap Base S Core f i (x k), hmem⟩ := by
                  apply congrArg q
                  apply Subtype.ext
                  exact hk
            _ = copies i (x k) := q_copy i hiJ (x k) hmem
    · intro K hK
      let Small :=
        (Attachment.attach Base S Core f).induce
          (↑Test : Set (Attachment.Vertex S (W := W) (I := I)))
      let incTest : Embedding Small (Attachment.attach Base S Core f) :=
        inclusion (Attachment.attach Base S Core f) (↑Test : Set _)
      let incK₀ : Embedding (Small.induce K) Small :=
        inclusion Small K
      let incK : Embedding (Small.induce K) (Attachment.attach Base S Core f) :=
        incTest.comp incK₀
      by_cases hAllCore :
          ∀ z : ↥K, ∃ w : W, z.1.1 = Sum.inl w
      · let coreR : Embedding (Core.induce (↑R : Set W))
            (Attachment.attach Base S Core f) :=
          (Attachment.coreEmbedding Base S Core f).comp
            (inclusion Core (↑R : Set W))
        have hrange :
            ∀ z : ↥K, ∃ r : ↥(↑R : Set W), incK z = coreR r := by
          intro z
          obtain ⟨w, hw⟩ := hAllCore z
          have hwT :
              (Sum.inl w :
                Attachment.Vertex S (W := W) (I := I)) ∈ Test := by
            have hm := z.1.2
            rw [hw] at hm
            exact hm
          let r : ↥(↑R : Set W) := ⟨w, hCoreTest w hwT⟩
          refine ⟨r, ?_⟩
          change z.1.1 = Sum.inl r.1
          exact hw
        let eKR : Embedding (Small.induce K) (Core.induce (↑R : Set W)) :=
          incK.factorThroughRange coreR hrange
        obtain ⟨e₀, he₀⟩ :=
          hg.after_irreducible_embedding hK eKR
        refine ⟨coreT.comp e₀, ?_⟩
        intro z
        have hz := Classical.choose_spec (hrange z)
        let r : ↥(↑R : Set W) := eKR z
        have hcoreEq : z.1.1 = Sum.inl r.1 := by
          change incK z = coreR r at hz
          exact hz
        have hrTest :
            (Sum.inl r.1 :
              Attachment.Vertex S (W := W) (I := I)) ∈ Test := by
          have hm := z.1.2
          rw [hcoreEq] at hm
          exact hm
        change coreT (e₀ z) = q z.1
        rw [he₀ z]
        calc
          coreT (g (eKR z)) =
              coreT (g ⟨r.1, hCoreTest r.1 hrTest⟩) := by
                apply congrArg coreT
                apply congrArg g
                apply Subtype.ext
                rfl
          _ = q z.1 := by
                symm
                rw [hcoreEq]
                simpa using q_inl r.1 hrTest
      · push Not at hAllCore
        obtain ⟨z₀, hz₀⟩ := hAllCore
        cases hzval : z₀.1.1 with
        | inl w =>
            exact (hz₀ w hzval).elim
        | inr ix =>
            let i : I := ix.1
            let x₀ : {x : VB // x ∉ S} := ix.2
            have hiJ : i ∈ J := by
              apply hActive i x₀
              have hm := z₀.1.2
              simpa [i, x₀, hzval] using hm
            let Rng : Set (Attachment.Vertex S (W := W) (I := I)) :=
              Set.range incK
            have hRng : ((Attachment.attach Base S Core f).induce Rng).Irreducible :=
              hK.range_embedding incK
            rcases Attachment.irreducible_core_or_copy
                (B := Base) (S := S) (D := Core) (f := f) Rng hRng with
              hcore | ⟨j, hcopy⟩
            · let rz : Rng := ⟨incK z₀, ⟨z₀, rfl⟩⟩
              obtain ⟨w, hw⟩ := hcore rz
              change z₀.1.1 = Sum.inl w at hw
              rw [hzval] at hw
              simp at hw
            · have hji : j = i := by
                let rz : Rng := ⟨incK z₀, ⟨z₀, rfl⟩⟩
                obtain ⟨b, hb⟩ := hcopy rz
                change z₀.1.1 =
                  Attachment.copyMap Base S Core f j b at hb
                have hleft :
                    Attachment.copyMap Base S Core f i x₀.1 =
                      Attachment.copyMap Base S Core f j b := by
                  calc
                    Attachment.copyMap Base S Core f i x₀.1 =
                        Sum.inr (i, x₀) := by
                          exact Attachment.copyMap_not_mem i x₀.1 x₀.2
                    _ = z₀.1.1 := hzval.symm
                    _ = Attachment.copyMap Base S Core f j b := hb
                exact Attachment.index_eq_of_outside x₀.2 hleft
              subst j
              have hrange :
                  ∀ z : ↥K, ∃ b : VB,
                    incK z = Attachment.copyEmbedding Base S Core f i b := by
                intro z
                let rz : Rng := ⟨incK z, ⟨z, rfl⟩⟩
                obtain ⟨b, hb⟩ := hcopy rz
                exact ⟨b, hb⟩
              let eB : Embedding (Small.induce K) Base :=
                incK.factorThroughRange
                  (Attachment.copyEmbedding Base S Core f i) hrange
              refine ⟨(copies i).comp eB, ?_⟩
              intro z
              have hz := Classical.choose_spec (hrange z)
              have hmem :
                  Attachment.copyMap Base S Core f i (eB z) ∈ Test := by
                change
                  (Attachment.copyEmbedding Base S Core f i) (eB z) ∈ Test
                rw [← hz]
                exact z.1.2
              change copies i (eB z) = q z.1
              symm
              calc
                q z.1 =
                    q ⟨Attachment.copyMap Base S Core f i (eB z), hmem⟩ := by
                      apply congrArg q
                      apply Subtype.ext
                      change z.1.1 =
                        Attachment.copyMap Base S Core f i (eB z)
                      exact hz
                _ = copies i (eB z) := q_copy i hiJ (eB z) hmem

  refine ⟨Y, T, hTree, q, hq, ?_⟩
  intro α
  let Rng : Set (Attachment.Vertex S (W := W) (I := I)) :=
    Set.range α
  have hRng :
      ((Attachment.attach Base S Core f).induce Rng).Irreducible :=
    hControl.range_embedding α
  rcases Attachment.irreducible_core_or_copy
      (B := Base) (S := S) (D := Core) (f := f) Rng hRng with
    hcore | ⟨i, hcopy⟩
  · have hrange : ∀ a : UA, ∃ w : W,
        α a = Attachment.coreEmbedding Base S Core f w := by
      intro a
      let z : Rng := ⟨α a, ⟨a, rfl⟩⟩
      obtain ⟨w, hw⟩ := hcore z
      exact ⟨w, hw⟩
    let αCore : Embedding Control Core :=
      α.factorThroughRange (Attachment.coreEmbedding Base S Core f) hrange
    obtain ⟨α₀, hα₀⟩ := hctrl αCore
    refine ⟨coreT.comp α₀, ?_⟩
    intro a ha
    have hαcore := Classical.choose_spec (hrange a)
    have hmemR : αCore a ∈ R := by
      apply hCoreTest (αCore a)
      change Sum.inl (αCore a) ∈ Test
      calc
        Sum.inl (αCore a) = α a := hαcore.symm
        _ ∈ Test := ha
    obtain ⟨a', ha'⟩ := hα₀ a hmemR
    refine ⟨a', ?_⟩
    have htest :
        (Sum.inl (αCore a) :
          Attachment.Vertex S (W := W) (I := I)) ∈ Test := by
      simpa [hαcore] using ha
    calc
      q ⟨α a, ha⟩ =
          q ⟨Sum.inl (αCore a), htest⟩ := by
            apply congrArg q
            apply Subtype.ext
            exact hαcore
      _ = coreT (g ⟨αCore a, hmemR⟩) := q_inl (αCore a) htest
      _ = coreT (α₀ a') := congrArg coreT ha'
  · have hcopyA : ∃ i : I, ∀ a : UA, ∃ b : VB,
        α a = Attachment.copyMap Base S Core f i b := by
      refine ⟨i, ?_⟩
      intro a
      let z : Rng := ⟨α a, ⟨a, rfl⟩⟩
      exact hcopy z
    obtain ⟨j, hj, β, hβ⟩ := hTrace α hcopyA
    refine ⟨(copies j).comp β, ?_⟩
    intro a ha
    have hEq := hβ a ha
    have hmem :
        Attachment.copyMap Base S Core f j (β a) ∈ Test := by
      rw [← hEq]
      exact ha
    refine ⟨a, ?_⟩
    calc
      q ⟨α a, ha⟩ =
          q ⟨Attachment.copyMap Base S Core f j (β a), hmem⟩ := by
            apply congrArg q
            apply Subtype.ext
            exact hEq
      _ = copies j (β a) := q_copy j hj (β a) hmem

end StructuralRamsey.RelStructure.LocallyTreeLike
