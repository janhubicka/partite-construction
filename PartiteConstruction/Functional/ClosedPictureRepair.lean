import PartiteConstruction.Functional.ClosedPicture
import PartiteConstruction.Partite.Picture

/-! # Disjoint-copy repair for arbitrary projected pictures

An ordinary Picture witness can be repaired without freely attaching along a
non-U-closed support.  The repair uses a disjoint union of copies of the current
partite system, indexed by its embeddings into the ordinary Picture witness.
For positive-arity functions every indexed copy is U-closed, and
U-transversality is inherited from the copied system.

A finite vector-colouring of A-copies in the ordinary witness then chooses an
index whose corresponding disjoint copy is monochromatic for the original
closed colouring.  This avoids the non-closed free-attachment obstruction.
-/
namespace StructuralRamsey.Partite.ClosedRepair

open RelStructure Structure

universe u v
variable {L : Language.{u}} {P V I : Type v}

/-- Disjoint union of copies of a partite system, preserving its original
partition labels. -/
def disjointCopies (B : Partite.System L.graph P V) (I : Type v) :
    Partite.System L.graph P (I × V) where
  rel R z := ∃ i x, B.rel R x ∧ z = (fun v => (i, v)) ∘ x
  part iv := B.part iv.2
  transversal R z hz k l hkl := by
    obtain ⟨i, x, hx, rfl⟩ := hz
    have hxy := B.transversal R x hx k l hkl
    exact congrArg (fun v => (i, v)) hxy

/-- The canonical indexed copy as a partite embedding. -/
def copyEmbedding
    (B : Partite.System L.graph P V) (I : Type v) (i : I) :
    Partite.Embedding B (disjointCopies B I) where
  toFun v := (i, v)
  injective _ _ h := congrArg Prod.snd h
  map_rel_iff R x := by
    constructor
    · rintro ⟨j, y, hy, h⟩
      have heq : x = y := funext (fun k => congrArg Prod.snd (congrFun h k))
      simpa only [heq] using hy
    · intro hx
      exact ⟨i, x, hx, rfl⟩
  map_part _ := rfl

/-- For positive-arity function symbols an indexed copy in the disjoint union
is U-closed: an input coordinate fixes the copy index. -/
def closedCopyEmbedding
    (B : Partite.System L.graph P V) (I : Type v)
    (hpos : L.PositiveFuncArity) (i : I) :
    Partite.Closed.Embedding B (disjointCopies B I) := by
  let pe := copyEmbedding B I i
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  change
    (disjointCopies B I).rel (.inr F)
      (Structure.funcTuple (pe ∘ x) y) at hy
  rcases hy with ⟨j, t, ht, heq⟩
  have hidx : j = i := by
    have hk := congrFun heq (Fin.castSucc k0)
    have hk' := congrArg Prod.fst hk
    have hij : i = j := by
      calc
        i = (Structure.funcTuple (pe ∘ x) y (Fin.castSucc k0)).1 := by
          rw [Structure.funcTuple_castSucc]
          rfl
        _ = (((fun v => (j, v)) ∘ t) (Fin.castSucc k0)).1 := hk'
        _ = j := by rfl
    exact hij.symm
  subst j
  let args : Fin (L.funcArity F) → V :=
    fun k => t (Fin.castSucc k)
  let z : V := t (Fin.last (L.funcArity F))
  have hargs : x = args := by
    funext k
    have hk := congrFun heq (Fin.castSucc k)
    have hk' := congrArg Prod.snd hk
    calc
      x k = (Structure.funcTuple (pe ∘ x) y (Fin.castSucc k)).2 := by
        rw [Structure.funcTuple_castSucc]
        rfl
      _ = (((fun v => (i, v)) ∘ t) (Fin.castSucc k)).2 := hk'
      _ = t (Fin.castSucc k) := by rfl
      _ = args k := by rfl
  have heta : Structure.funcTuple args z = t := by
    simpa [args, z, Language.graph] using
      (Structure.funcTuple_eta (t := t))
  have hrel : B.rel (.inr F) (Structure.funcTuple x z) := by
    rw [hargs, heta]
    exact ht
  refine ⟨z, hrel, ?_⟩
  have hout := congrFun heq (Fin.last (L.funcArity F))
  calc
    pe z = (i, z) := rfl
    _ = (((fun v => (i, v)) ∘ t) (Fin.last (L.funcArity F))) := by rfl
    _ = Structure.funcTuple (pe ∘ x) y (Fin.last (L.funcArity F)) :=
      hout.symm
    _ = y := Structure.funcTuple_last _ _

/-- Disjoint copies inherit U-transversality from the copied system. -/
theorem disjointCopies_uTransversal
    (B : Partite.System L.graph P V) (I : Type v)
    (hpos : L.PositiveFuncArity)
    (hU : B.FunctionOutputTransversal) :
    (disjointCopies B I).FunctionOutputTransversal := by
  intro F x y z hy hz hp
  have hF : 0 < L.funcArity F := hpos F
  let k0 : Fin (L.funcArity F) := ⟨0, hF⟩
  rcases hy with ⟨i, a, ha, heqa⟩
  rcases hz with ⟨j, b, hb, heqb⟩
  have hya := congrFun heqa (Fin.castSucc k0)
  have hzb := congrFun heqb (Fin.castSucc k0)
  have hidxa : (x k0).1 = i := by
    calc
      (x k0).1 = (Structure.funcTuple x y (Fin.castSucc k0)).1 := by
        rw [Structure.funcTuple_castSucc]
      _ = (((fun v => (i, v)) ∘ a) (Fin.castSucc k0)).1 :=
        congrArg Prod.fst hya
      _ = i := by rfl
  have hidxb : (x k0).1 = j := by
    calc
      (x k0).1 = (Structure.funcTuple x z (Fin.castSucc k0)).1 := by
        rw [Structure.funcTuple_castSucc]
      _ = (((fun v => (j, v)) ∘ b) (Fin.castSucc k0)).1 :=
        congrArg Prod.fst hzb
      _ = j := by rfl
  have hij : j = i := hidxb.symm.trans hidxa
  rw [hij] at heqb hzb
  let ay : V := a (Fin.last (L.funcArity F))
  let bz : V := b (Fin.last (L.funcArity F))
  have houta := congrFun heqa (Fin.last (L.funcArity F))
  have houtb := congrFun heqb (Fin.last (L.funcArity F))
  have hyEq : y = (i, ay) := by
    calc
      y = Structure.funcTuple x y (Fin.last (L.funcArity F)) := by
        rw [Structure.funcTuple_last]
      _ = (((fun v => (i, v)) ∘ a)
          (Fin.last (L.funcArity F))) := houta
      _ = (i, ay) := by rfl
  have hzEq : z = (i, bz) := by
    calc
      z = Structure.funcTuple x z (Fin.last (L.funcArity F)) := by
        rw [Structure.funcTuple_last]
      _ = (((fun v => (i, v)) ∘ b)
          (Fin.last (L.funcArity F))) := houtb
      _ = (i, bz) := by rfl
  have hpB : B.part ay = B.part bz := by
    have hp' := hp
    rw [hyEq, hzEq] at hp'
    exact hp'
  have heq : ay = bz := by
    let argsA : Fin (L.funcArity F) → V :=
      fun k => a (Fin.castSucc k)
    let argsB : Fin (L.funcArity F) → V :=
      fun k => b (Fin.castSucc k)
    have hargs : argsA = argsB := by
      funext k
      have hka := congrArg Prod.snd (congrFun heqa (Fin.castSucc k))
      have hkb := congrArg Prod.snd (congrFun heqb (Fin.castSucc k))
      have hka' : (x k).2 = a (Fin.castSucc k) := by
        calc
          (x k).2 =
              (Structure.funcTuple x y (Fin.castSucc k)).2 := by
                rw [Structure.funcTuple_castSucc]
          _ = (((fun v => (i, v)) ∘ a) (Fin.castSucc k)).2 := hka
          _ = a (Fin.castSucc k) := by rfl
      have hkb' : (x k).2 = b (Fin.castSucc k) := by
        calc
          (x k).2 =
              (Structure.funcTuple x z (Fin.castSucc k)).2 := by
                rw [Structure.funcTuple_castSucc]
          _ = (((fun v => (i, v)) ∘ b) (Fin.castSucc k)).2 := hkb
          _ = b (Fin.castSucc k) := by rfl
      exact hka'.symm.trans hkb'
    have ha' : B.rel (.inr F) (Structure.funcTuple argsA ay) := by
      have heta : Structure.funcTuple argsA ay = a := by
        simpa [argsA, ay, Language.graph] using
          (Structure.funcTuple_eta (t := a))
      rw [heta]
      exact ha
    have hb0 : B.rel (.inr F) (Structure.funcTuple argsB bz) := by
      have heta : Structure.funcTuple argsB bz = b := by
        simpa [argsB, bz, Language.graph] using
          (Structure.funcTuple_eta (t := b))
      rw [heta]
      exact hb
    have hb' : B.rel (.inr F) (Structure.funcTuple argsA bz) := by
      rw [hargs]
      exact hb0
    exact hU F argsA ay bz ha' hb' hpB
  calc
    y = (i, ay) := hyEq
    _ = (i, bz) := congrArg (fun q => (i, q)) heq
    _ = z := hzEq.symm


/-- Every relation tuple of O is carried by one closed partite copy of B.
This is the precise coverage hypothesis used in the recursive-construction
paragraph of the survey. -/
def TupleCoveredByClosedCopies
    {W : Type v}
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    {J : Type v}
    (g : J → Partite.Closed.Embedding B O) : Prop :=
  ∀ (R : L.graph.Symbol) (t : Fin (L.graph.arity R) → W),
    O.rel R t →
      ∃ j : J, ∃ q : Fin (L.graph.arity R) → V,
        B.rel R q ∧ t = g j ∘ q

/-- The manuscript's tuple-coverage condition really does imply
U-transversality.  The proof uses coverage for one output tuple and closedness
of the covering copy to pull the competing output into the same copy. -/
theorem uTransversal_of_tupleCovered
    {W J : Type v}
    (B : Partite.System L.graph P V)
    (O : Partite.System L.graph P W)
    (g : J → Partite.Closed.Embedding B O)
    (hB : B.FunctionOutputTransversal)
    (hCover : TupleCoveredByClosedCopies B O g) :
    O.FunctionOutputTransversal := by
  intro F x y z hy hz hp
  obtain ⟨j, q, hq, heq⟩ :=
    hCover (.inr F) (Structure.funcTuple x y) hy
  let args : Fin (L.funcArity F) → V :=
    fun k => q (Fin.castSucc k)
  let outY : V := q (Fin.last (L.funcArity F))
  have hqEta : Structure.funcTuple args outY = q := by
    simpa [args, outY, Language.graph] using
      (Structure.funcTuple_eta (t := q))
  have hBrelY : B.rel (.inr F) (Structure.funcTuple args outY) := by
    rw [hqEta]
    exact hq
  have hinputs : ∀ k, g j (args k) = x k := by
    intro k
    have hk := congrFun heq (Fin.castSucc k)
    rw [Structure.funcTuple_castSucc] at hk
    change x k = g j (args k) at hk
    exact hk.symm
  have hyImage : g j outY = y := by
    have hk := congrFun heq (Fin.last (L.funcArity F))
    rw [Structure.funcTuple_last] at hk
    change y = g j outY at hk
    exact hk.symm
  have hzTarget :
      O.rel (.inr F)
        (Structure.funcTuple (g j ∘ args) z) := by
    have hargsEq : g j ∘ args = x := by
      funext k
      exact hinputs k
    rw [hargsEq]
    exact hz
  obtain ⟨outZ, hBrelZ, hzImage⟩ :=
    (g j).2 F args z hzTarget
  have hpB : B.part outY = B.part outZ := by
    calc
      B.part outY = O.part (g j outY) := ((g j).1.map_part outY).symm
      _ = O.part y := congrArg O.part hyImage
      _ = O.part z := hp
      _ = O.part (g j outZ) := congrArg O.part hzImage.symm
      _ = B.part outZ := (g j).1.map_part outZ
  have hout : outY = outZ :=
    hB F args outY outZ hBrelY hBrelZ hpB
  calc
    y = g j outY := hyImage.symm
    _ = g j outZ := congrArg (g j) hout
    _ = z := hzImage


/-- Keep exactly those relation tuples of C which lie inside some closed
partite copy of B.  The carrier and part map are unchanged. -/
noncomputable def copyGenerated
    {W : Type v}
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W) :
    Partite.System L.graph P W where
  rel R t :=
    ∃ e : Partite.Closed.Embedding B C,
      ∃ q : Fin (L.graph.arity R) → V,
        B.rel R q ∧ t = e ∘ q
  part := C.part
  transversal R t ht k l hp := by
    rcases ht with ⟨e, q, hq, heq⟩
    have hC : C.rel R t := by
      rw [heq]
      exact (e.1.toEmbedding.map_rel_iff R q).mpr hq
    exact C.transversal R t hC k l hp

/-- Every closed B-copy of C survives as a closed B-copy of the
copy-generated reduct. -/
noncomputable def generatedCopy
    {W : Type v}
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W)
    (e : Partite.Closed.Embedding B C) :
    Partite.Closed.Embedding B (copyGenerated B C) := by
  let pe : Partite.Embedding B (copyGenerated B C) := {
    toFun := e
    injective := e.1.toEmbedding.injective
    map_rel_iff := by
      intro R q
      constructor
      · rintro ⟨d, r, hr, hEq⟩
        have hC0 : C.rel R (d ∘ r) :=
          (d.1.toEmbedding.map_rel_iff R r).mpr hr
        have hC : C.rel R (e ∘ q) := by
          rw [hEq]
          exact hC0
        exact (e.1.toEmbedding.map_rel_iff R q).mp hC
      · intro hq
        exact ⟨e, q, hq, rfl⟩
    map_part := e.1.map_part
  }
  refine ⟨pe, ?_⟩
  intro F x y hy
  have hyC :
      C.rel (.inr F)
        (Structure.funcTuple (e ∘ x) y) := by
    rcases hy with ⟨d, q, hq, hEq⟩
    have h : C.rel (.inr F) (d ∘ q) :=
      (d.1.toEmbedding.map_rel_iff (.inr F) q).mpr hq
    change C.rel (.inr F)
      (Structure.funcTuple (pe ∘ x) y)
    rw [hEq]
    exact h
  obtain ⟨z, hz, hzy⟩ := e.2 F x y hyC
  exact ⟨z, hz, hzy⟩

/-- By construction, every tuple in the copy-generated reduct is covered by
one of its surviving closed B-copies. -/
theorem copyGenerated_tupleCovered
    {W : Type v}
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W) :
    TupleCoveredByClosedCopies B (copyGenerated B C)
      (fun e : Partite.Closed.Embedding B C =>
        generatedCopy B C e) := by
  intro R t ht
  rcases ht with ⟨e, q, hq, hEq⟩
  exact ⟨e, q, hq, hEq⟩

/-- Copy-generation repairs U-transversality whenever the copied structure B
is U-transversal, regardless of whether C itself is U-transversal. -/
theorem copyGenerated_uTransversal
    {W : Type v}
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W)
    (hB : B.FunctionOutputTransversal) :
    (copyGenerated B C).FunctionOutputTransversal := by
  exact uTransversal_of_tupleCovered
    B (copyGenerated B C)
    (fun e : Partite.Closed.Embedding B C => generatedCopy B C e)
    hB (copyGenerated_tupleCovered B C)

/-- Closed A-embeddings into C which are also embeddings into the
copy-generated reduct. -/
def LiftableToGenerated
    {U W : Type v}
    (A : Partite.System L.graph P U)
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W)
    (e : Partite.Closed.Embedding A C) : Prop :=
  ∃ d : Partite.Closed.Embedding A (copyGenerated B C),
    ∀ x, d x = e x

/-- A closed embedding into the generated reduct is uniquely determined by
its underlying map to C. -/
theorem liftable_unique
    {U W : Type v}
    {A : Partite.System L.graph P U}
    {B : Partite.System L.graph P V}
    {C : Partite.System L.graph P W}
    {e : Partite.Closed.Embedding A C}
    {d₁ d₂ : Partite.Closed.Embedding A (copyGenerated B C)}
    (h₁ : ∀ x, d₁ x = e x)
    (h₂ : ∀ x, d₂ x = e x) :
    d₁ = d₂ := by
  apply Partite.Closed.Embedding.ext
  intro x
  exact (h₁ x).trans (h₂ x).symm

/-- A closed Ramsey arrow survives copy-generation.  Embeddings which do not
lift to the generated reduct receive a default colour; the monochromatic
B-copy returned in C always lifts because its own relations were retained. -/
theorem copyGenerated_arrow
    {U W : Type v}
    (A : Partite.System L.graph P U)
    (B : Partite.System L.graph P V)
    (C : Partite.System L.graph P W)
    (κ : Type*) [Nonempty κ]
    (h : Partite.Closed.Arrow A B C κ) :
    Partite.Closed.Arrow A B (copyGenerated B C) κ := by
  classical
  intro χ
  let θ : Partite.Closed.Embedding A C → κ := fun e =>
    if he : LiftableToGenerated A B C e then
      χ (Classical.choose he)
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨f, hf⟩ := h θ
  let fg : Partite.Closed.Embedding B (copyGenerated B C) :=
    generatedCopy B C f
  refine ⟨fg, ?_⟩
  intro e₁ e₂
  let c₁ : Partite.Closed.Embedding A C :=
    Partite.Closed.Embedding.comp f e₁
  let c₂ : Partite.Closed.Embedding A C :=
    Partite.Closed.Embedding.comp f e₂
  let d₁ : Partite.Closed.Embedding A (copyGenerated B C) :=
    Partite.Closed.Embedding.comp fg e₁
  let d₂ : Partite.Closed.Embedding A (copyGenerated B C) :=
    Partite.Closed.Embedding.comp fg e₂
  have hd₁ : ∀ x, d₁ x = c₁ x := fun _ => rfl
  have hd₂ : ∀ x, d₂ x = c₂ x := fun _ => rfl
  have hl₁ : LiftableToGenerated A B C c₁ := ⟨d₁, hd₁⟩
  have hl₂ : LiftableToGenerated A B C c₂ := ⟨d₂, hd₂⟩
  have hθ₁ : θ c₁ = χ d₁ := by
    simp only [θ, dif_pos hl₁]
    congr 1
    exact liftable_unique
      (e := c₁)
      (Classical.choose_spec hl₁) hd₁
  have hθ₂ : θ c₂ = χ d₂ := by
    simp only [θ, dif_pos hl₂]
    congr 1
    exact liftable_unique
      (e := c₂)
      (Classical.choose_spec hl₂) hd₂
  calc
    χ (Partite.Closed.Embedding.comp fg e₁) = χ d₁ := rfl
    _ = θ c₁ := hθ₁.symm
    _ = θ c₂ := hf e₁ e₂
    _ = χ d₂ := hθ₂
    _ = χ (Partite.Closed.Embedding.comp fg e₂) := rfl

end StructuralRamsey.Partite.ClosedRepair
