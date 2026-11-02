import PartiteConstruction.Functional.HJThreeLineNativeFullAttachmentC7

/-!
# Track D: exact three-line C7 from any sequential native Picture history

The full finite native attachment in the preceding module uses the
simultaneous three-index constructor. The actual EHN Ramsey Picture
uses a SEQUENTIAL list of full copies. We do not assume these carriers
are definitionally equal or manufacture an isomorphism.

Instead we prove the precise universal TRANSFER statement. In ANY
native functional-partite output T, suppose the initial true
two-letter Hales--Jewett power embeds FULLY and the three old P5
copies embed FULLY, with their exact selected supports identified
with the prescribed HJ line embeddings. Then the seven old/exterior
and core vertices form an odd closed walk in T, and T cannot be
two-coloured.

No separation assumption between copied exterior vertices is
necessary: if the seven names happened to collide, the seven
relation edges would still prevent two-colouring. No temporary
multi-fibre functions or total-fibre global maps are introduced.

The existence of such coherent core/copy embeddings is proved for
actual sequential full attachment lists by `NativeFullAttachmentList`.
This module intentionally states the conditional transfer without
assuming that independent source-geometry PR has merged.
-/

namespace StructuralRamsey.Structure.TrackD.NativeThreeLineC7

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackD.NativeTwoLetterHJ

/-- A checked obstruction for EVERY genuine native full functional
stage with three prescribed FULL copied P5s and canonical HJ root
overlaps, including the actual EHN sequential attachment output.

There is no quantified unsupported relative strict B-tree target.
This is exclusively an obstruction to naive history-independent
native full-attachment/strict-tree locality. -/
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
    have hs : oldSystem.toStructure.rel () tup := by
      change oldEdge a z
      exact h
    have hm := (b.toEmbedding.map_rel_iff () tup).mpr hs
    simpa only [E, tup, Function.comp_apply] using hm
  have coreEdge :
      E (j (Induced.lineMap W0 (false, false)))
        (j (Induced.lineMap W1 (true, true))) := by
    let tup : Fin 2 → Induced.Vertex R 2 :=
      fun k => if k = 0 then Induced.lineMap W0 (false, false)
        else Induced.lineMap W1 (true, true)
    have hm := (j.toEmbedding.map_rel_iff () tup).mpr
      NativeTwoLetterHJ.native_core_cross_edge
    simpa only [E, tup, Function.comp_apply] using hm

  have imageA (b : FunctionalPartite.Embedding oldSystem T)
      (i : Fin 3) (hb : ∀ x : support, b x.1 = j (maps i x)) :
      b 0 = j (Induced.lineMap (chosenLine i) (false, false)) := by
    calc
      b 0 = j (maps i ⟨0, by decide⟩) :=
        hb ⟨0, by decide⟩
      _ = _ := congrArg j (maps_a0 i)
  have imageB (b : FunctionalPartite.Embedding oldSystem T)
      (i : Fin 3) (hb : ∀ x : support, b x.1 = j (maps i x)) :
      b 3 = j (Induced.lineMap (chosenLine i) (true, true)) := by
    calc
      b 3 = j (maps i ⟨3, by decide⟩) :=
        hb ⟨3, by decide⟩
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
    exact copyEdge b0 4 0 (by decide)
  have h12 : E v1 v2 := coreEdge
  have h23 : E v2 v3 := by
    change E (j (Induced.lineMap W1 (true, true))) (b1 4)
    rw [← imageB b1 1 h1]
    exact copyEdge b1 3 4 (by decide)
  have h34 : E v3 v4 := by
    change E (b1 4) (j (Induced.lineMap W1 (false, false)))
    rw [← imageA b1 1 h1]
    exact copyEdge b1 4 0 (by decide)
  have h45 : E v4 v5 := by
    change E (j (Induced.lineMap W1 (false, false))) (b2 4)
    have heq : Induced.lineMap W1 (false, false) =
        Induced.lineMap W2 (false, false) :=
      NativeTwoLetterHJ.W1_a0.trans NativeTwoLetterHJ.W2_a0.symm
    rw [heq, ← imageA b2 2 h2]
    exact copyEdge b2 0 4 (by decide)
  have h56 : E v5 v6 := by
    change E (b2 4) (j (Induced.lineMap W2 (true, true)))
    rw [← imageB b2 2 h2]
    exact copyEdge b2 4 3 (by decide)
  have h60 : E v6 v0 := by
    change E (j (Induced.lineMap W2 (true, true))) (b0 4)
    have heq : Induced.lineMap W2 (true, true) =
        Induced.lineMap W0 (true, true) :=
      NativeTwoLetterHJ.W2_b1.trans NativeTwoLetterHJ.W0_b1.symm
    rw [heq, ← imageB b0 0 h0]
    exact copyEdge b0 3 4 (by decide)

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

end StructuralRamsey.Structure.TrackD.NativeThreeLineC7
