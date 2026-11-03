import PartiteConstruction.Functional.NativeFullAttachmentList
import PartiteConstruction.Functional.HJThreeLineNativeFullAttachmentC7

/-!
# Track D: genuine SEQUENTIAL three-line native HJ attachments have a C7 obstruction

The simultaneous three-copy attachment in HJThreeLineNativeFullAttachmentC7
has an actual native graph odd cycle. The Ramsey Picture instead performs a
finite SEQUENCE of full native attachments. We do not identify those two
carriers by fiat.

The verified FunctionalPartite.attachList_full returns a real sequential
native functional partite System, a full initial HJ-core embedding, and full
OLD-P5 copy embeddings for every selected line, all agreeing exactly with
the prescribed HJ embeddings on the selected function-closed support.

First, a separate theorem proves the seven-edge parity obstruction for
ANY such family of full embeddings. Then the genuine sequential construction
instantiates that theorem for the three actual HJ lines (b,p), (p,a), (p,p).

The resulting sequential output cannot be properly two-coloured, and has no
weak graph homomorphism back to the OLD P5. The latter excludes in particular
an EHN shadow. This is NOT a failure of the full history-sensitive rank
successor lemma: the rank-3 predecessor-locality of its K3 control is false.
No total-fibre projection or arbitrary-stage mixed-root extension is used.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

/-- Three FULL old P5 copies attached along the true W0/W1/W2
Hales--Jewett support maps already force a seven-edge odd walk, in
ANY genuine native functional-partite target System, whether the
copies were simultaneously or sequentially attached.

Full embeddings are essential; no graph-only or U-closed surrogate
is introduced. The root equations identify exactly the old selected
support, never its function-generated closure. -/
theorem any_three_full_copies_not_twoColorable
    {X : Type}
    (T : FunctionalPartite.System Lang (Fin 3) X)
    (j : FunctionalPartite.Embedding Core T)
    (b0 b1 b2 : FunctionalPartite.Embedding oldSystem T)
    (h0 : ∀ x : support, b0 x.1 = j (maps 0 x))
    (h1 : ∀ x : support, b1 x.1 = j (maps 1 x))
    (h2 : ∀ x : support, b2 x.1 = j (maps 2 x)) :
    ¬ ∃ c : X → Bool,
      ∀ a b : X,
        T.toStructure.rel () (fun k : Fin 2 =>
          if k = 0 then a else b) → c a ≠ c b := by
  let E : X → X → Prop := fun a b =>
    T.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then a else b)
  have copyEdge (b : FunctionalPartite.Embedding oldSystem T)
      (a z : Fin 5) (h : oldEdge a z) : E (b a) (b z) := by
    let tup : Fin 2 → Fin 5 :=
      fun k => if k = 0 then a else z
    have hSrc : oldSystem.toStructure.rel () tup := by
      change oldEdge a z
      exact h
    have hm := (b.toEmbedding.map_rel_iff () tup).mpr hSrc
    change T.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then b a else b z)
    have hTuple :
        (fun k : Fin 2 => if k = 0 then b a else b z) =
        (b.toFun ∘ tup) := by
      funext k
      by_cases hk : k = 0 <;> simp [tup, hk, Function.comp_apply]
    rw [hTuple]
    exact hm
  have coreEdge :
      E (j (Induced.lineMap W0 (false, false)))
        (j (Induced.lineMap W1 (true, true))) := by
    let tup : Fin 2 → Induced.Vertex R 2 :=
      fun k => if k = 0 then Induced.lineMap W0 (false, false)
        else Induced.lineMap W1 (true, true)
    have hSrc : Core.toStructure.rel () tup :=
      NativeTwoLetterHJ.native_core_cross_edge
    have hm := (j.toEmbedding.map_rel_iff () tup).mpr hSrc
    change T.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then j (Induced.lineMap W0 (false, false))
        else j (Induced.lineMap W1 (true, true)))
    have hTuple :
        (fun k : Fin 2 =>
          if k = 0 then j (Induced.lineMap W0 (false, false))
            else j (Induced.lineMap W1 (true, true))) =
        (j.toFun ∘ tup) := by
      funext k
      by_cases hk : k = 0 <;> simp [tup, hk, Function.comp_apply]
    rw [hTuple]
    exact hm

  have imageA (b : FunctionalPartite.Embedding oldSystem T)
      (i : Fin 3) (hb : ∀ x : support, b x.1 = j (maps i x)) :
      b 0 = j (Induced.lineMap (chosenLine i) (false, false)) := by
    calc
      b 0 = j (maps i ⟨0, by simp [support]⟩) :=
        hb ⟨0, by simp [support]⟩
      _ = _ := congrArg j (maps_a0 i)
  have imageB (b : FunctionalPartite.Embedding oldSystem T)
      (i : Fin 3) (hb : ∀ x : support, b x.1 = j (maps i x)) :
      b 3 = j (Induced.lineMap (chosenLine i) (true, true)) := by
    calc
      b 3 = j (maps i ⟨3, by simp [support]⟩) :=
        hb ⟨3, by simp [support]⟩
      _ = _ := congrArg j (maps_b1 i)

  let v0 : X := b0 4
  let v1 : X := j (Induced.lineMap W0 (false, false))
  let v2 : X := j (Induced.lineMap W1 (true, true))
  let v3 : X := b1 4
  let v4 : X := j (Induced.lineMap W1 (false, false))
  let v5 : X := b2 4
  let v6 : X := j (Induced.lineMap W2 (true, true))

  have h01 : E v0 v1 := by
    change E (b0 4) (j (Induced.lineMap W0 (false, false)))
    rw [← imageA b0 0 h0]
    exact copyEdge b0 4 0 (by simp [oldEdge])
  have h12 : E v1 v2 := coreEdge
  have h23 : E v2 v3 := by
    change E (j (Induced.lineMap W1 (true, true))) (b1 4)
    rw [← imageB b1 1 h1]
    exact copyEdge b1 3 4 (by simp [oldEdge])
  have h34 : E v3 v4 := by
    change E (b1 4) (j (Induced.lineMap W1 (false, false)))
    rw [← imageA b1 1 h1]
    exact copyEdge b1 4 0 (by simp [oldEdge])
  have h45 : E v4 v5 := by
    change E (j (Induced.lineMap W1 (false, false))) (b2 4)
    have heq : Induced.lineMap W1 (false, false) =
        Induced.lineMap W2 (false, false) :=
      NativeTwoLetterHJ.W1_a0.trans NativeTwoLetterHJ.W2_a0.symm
    rw [heq, ← imageA b2 2 h2]
    exact copyEdge b2 0 4 (by simp [oldEdge])
  have h56 : E v5 v6 := by
    change E (b2 4) (j (Induced.lineMap W2 (true, true)))
    rw [← imageB b2 2 h2]
    exact copyEdge b2 4 3 (by simp [oldEdge])
  have h60 : E v6 v0 := by
    change E (j (Induced.lineMap W2 (true, true))) (b0 4)
    have heq : Induced.lineMap W2 (true, true) =
        Induced.lineMap W0 (true, true) :=
      NativeTwoLetterHJ.W2_b1.trans NativeTwoLetterHJ.W0_b1.symm
    rw [heq, ← imageB b0 0 h0]
    exact copyEdge b0 3 4 (by simp [oldEdge])

  rintro ⟨c, hc⟩
  have neq {x y : X} (h : E x y) : c x ≠ c y :=
    hc x y h
  have eq_of_ne_ne {x y z : Bool}
      (hxy : x ≠ y) (hyz : y ≠ z) : x = z := by
    cases x <;> cases y <;> cases z <;> simp_all
  have h02 : c v0 = c v2 :=
    eq_of_ne_ne (neq h01) (neq h12)
  have h24 : c v2 = c v4 :=
    eq_of_ne_ne (neq h23) (neq h34)
  have h46 : c v4 = c v6 :=
    eq_of_ne_ne (neq h45) (neq h56)
  exact (neq h60) (h02.trans (h24.trans h46)).symm

/-- An actual FINITE SEQUENCE of three full functional HJ
attachments exists whose output is not two-colourable. The
proof uses only the already checked native `attachList_full`;
no false isomorphism with the simultaneous attachment is assumed. -/
theorem sequential_threeLines_not_twoColorable :
    ∃ (X : Type) (T : FunctionalPartite.System Lang (Fin 3) X),
      ¬ ∃ c : X → Bool,
        ∀ a b : X,
          T.toStructure.rel () (fun k : Fin 2 =>
            if k = 0 then a else b) → c a ≠ c b := by
  classical
  obtain ⟨X, T, j, hcopies⟩ :=
    FunctionalPartite.attachList_full
      oldSystem support support_closed Core maps
      ([(0 : Fin 3), 1, 2] : List (Fin 3))
  obtain ⟨b0, h0⟩ := hcopies 0 (by simp)
  obtain ⟨b1, h1⟩ := hcopies 1 (by simp)
  obtain ⟨b2, h2⟩ := hcopies 2 (by simp)
  exact ⟨X, T,
    any_three_full_copies_not_twoColorable T j b0 b1 b2 h0 h1 h2⟩

/-- There is an actual sequential native HJ Picture output with
NO weak relation/function homomorphism to the old P5. In particular
no EHN part-preserving global retraction can exist for this history.

This is a genuine construction-side counterexample, but it does NOT
satisfy the strict predecessor-rank assumption of the n-pass theorem:
the three-part control already contains a triangle. -/
theorem sequential_threeLines_no_weak_projection_to_old :
    ∃ (X : Type) (T : FunctionalPartite.System Lang (Fin 3) X),
      ¬ ∃ f : X → Fin 5,
        T.toStructure.IsWeakHomomorphism oldSystem.toStructure f := by
  obtain ⟨X, T, hBad⟩ := sequential_threeLines_not_twoColorable
  refine ⟨X, T, ?_⟩
  rintro ⟨f, hf⟩
  apply hBad
  refine ⟨oldColor ∘ f, ?_⟩
  intro a b h
  have hm : oldSystem.toStructure.rel () (f ∘
        (fun k : Fin 2 => if k = 0 then a else b)) :=
    hf.1 () (fun k : Fin 2 => if k = 0 then a else b) h
  have hm' : oldSystem.toStructure.rel () (fun k : Fin 2 =>
      if k = 0 then f a else f b) := by
    have heq :
        (f ∘ (fun k : Fin 2 => if k = 0 then a else b)) =
        (fun k : Fin 2 => if k = 0 then f a else f b) := by
      funext k
      by_cases hk : k = 0 <;> simp [hk, Function.comp_apply]
    rw [heq] at hm
    exact hm
  change oldEdge (f a) (f b) at hm'
  exact oldColor_edge (f a) (f b) hm'

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7
