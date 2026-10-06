import PartiteConstruction.Functional.ClosedLocalTreeCompletion
import PartiteConstruction.Structure.FreeAmalgam

/-! # Restricting a full free amalgam to a closed induced substructure

A closed induced substructure of a full free amalgam is again a full free
amalgam: take the inverse image of the closed test in the two sides and in the
common root.  Because all four displayed maps are full embeddings, these
preimages are closed and the induced structures inherit the same free-amalgam
diagram.

This is the full relation/function counterpart of the relational
Attachment.decompose bookkeeping and is useful for binary EHN attachment
steps.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Embedding Root Left}
variable {sR : Embedding Root Right}
variable {iL : Embedding Left Whole}
variable {iR : Embedding Right Whole}

/-- Closed restriction of a concrete full free-amalgam diagram. -/
theorem induceClosed
    (hfree : IsFreeAmalgam sL sR iL iR)
    (S : Set C) (hS : Whole.IsClosed S) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    let hL : Left.IsClosed Lset := iL.preimage_isClosed S hS
    let hR : Right.IsClosed Rset := iR.preimage_isClosed S hS
    let hM : Root.IsClosed Mset := (iL.comp sL).preimage_isClosed S hS
    let LS := Left.induce Lset hL
    let RS := Right.induce Rset hR
    let MS := Root.induce Mset hM
    let WS := Whole.induce S hS
    ∃ (mL : Embedding MS LS) (mR : Embedding MS RS)
      (jL : Embedding LS WS) (jR : Embedding RS WS),
      IsFreeAmalgam mL mR jL jR := by
  classical
  dsimp only
  let Lset : Set E := iL ⁻¹' S
  let Rset : Set F := iR ⁻¹' S
  let Mset : Set H := (iL.comp sL) ⁻¹' S
  have hL : Left.IsClosed Lset :=
    iL.preimage_isClosed S hS
  have hR : Right.IsClosed Rset :=
    iR.preimage_isClosed S hS
  have hM : Root.IsClosed Mset :=
    (iL.comp sL).preimage_isClosed S hS
  let LS := Left.induce Lset hL
  let RS := Right.induce Rset hR
  let MS := Root.induce Mset hM
  let WS := Whole.induce S hS

  let incL : Embedding LS Left :=
    inclusion Left Lset hL
  let incR : Embedding RS Right :=
    inclusion Right Rset hR
  let incM : Embedding MS Root :=
    inclusion Root Mset hM
  let incW : Embedding WS Whole :=
    inclusion Whole S hS

  let mL0 : Embedding MS Left := sL.comp incM
  let mR0 : Embedding MS Right := sR.comp incM
  let jL0 : Embedding LS Whole := iL.comp incL
  let jR0 : Embedding RS Whole := iR.comp incR

  have hmLrange :
      ∀ x : Mset, ∃ y : Lset, mL0 x = incL y := by
    intro x
    let y : Lset := ⟨sL x.1, x.2⟩
    exact ⟨y, rfl⟩
  have hmRrange :
      ∀ x : Mset, ∃ y : Rset, mR0 x = incR y := by
    intro x
    have hxR : iR (sR x.1) ∈ S := by
      have hov :
          iL (sL x.1) = iR (sR x.1) :=
        (hfree.overlap (sL x.1) (sR x.1)).mpr
          ⟨x.1, rfl, rfl⟩
      rw [← hov]
      exact x.2
    let y : Rset := ⟨sR x.1, hxR⟩
    exact ⟨y, rfl⟩
  have hjLrange :
      ∀ x : Lset, ∃ y : S, jL0 x = incW y := by
    intro x
    exact ⟨⟨iL x.1, x.2⟩, rfl⟩
  have hjRrange :
      ∀ x : Rset, ∃ y : S, jR0 x = incW y := by
    intro x
    exact ⟨⟨iR x.1, x.2⟩, rfl⟩

  let mL : Embedding MS LS :=
    mL0.factorThroughClosedRange incL hmLrange
  let mR : Embedding MS RS :=
    mR0.factorThroughClosedRange incR hmRrange
  let jL : Embedding LS WS :=
    jL0.factorThroughClosedRange incW hjLrange
  let jR : Embedding RS WS :=
    jR0.factorThroughClosedRange incW hjRrange

  have hmLval (x : Mset) : (mL x).1 = sL x.1 := by
    have h :=
      Embedding.factorThroughClosedRange_spec
        mL0 incL hmLrange x
    exact h
  have hmRval (x : Mset) : (mR x).1 = sR x.1 := by
    have h :=
      Embedding.factorThroughClosedRange_spec
        mR0 incR hmRrange x
    exact h
  have hjLval (x : Lset) : (jL x).1 = iL x.1 := by
    have h :=
      Embedding.factorThroughClosedRange_spec
        jL0 incW hjLrange x
    exact h
  have hjRval (x : Rset) : (jR x).1 = iR x.1 := by
    have h :=
      Embedding.factorThroughClosedRange_spec
        jR0 incW hjRrange x
    exact h

  refine ⟨mL, mR, jL, jR, ?_⟩
  constructor
  · intro z
    rcases hfree.covers z.1 with ⟨a, ha⟩ | ⟨b, hb⟩
    · have haS : iL a ∈ S := by
        rw [← ha]
        exact z.2
      let aS : Lset := ⟨a, haS⟩
      refine Or.inl ⟨aS, ?_⟩
      apply Subtype.ext
      exact (hjLval aS).trans ha.symm
    · have hbS : iR b ∈ S := by
        rw [← hb]
        exact z.2
      let bS : Rset := ⟨b, hbS⟩
      refine Or.inr ⟨bS, ?_⟩
      apply Subtype.ext
      exact (hjRval bS).trans hb.symm
  · intro a b
    constructor
    · intro hab
      have hab0 : iL a.1 = iR b.1 := by
        calc
          iL a.1 = (jL a).1 := (hjLval a).symm
          _ = (jR b).1 := congrArg Subtype.val hab
          _ = iR b.1 := hjRval b
      obtain ⟨d, had, hbd⟩ :=
        (hfree.overlap a.1 b.1).mp hab0
      have hdS : iL (sL d) ∈ S := by
        rw [← had]
        exact a.2
      let dS : Mset := ⟨d, hdS⟩
      refine ⟨dS, ?_, ?_⟩
      · apply Subtype.ext
        calc
          (mL dS).1 = sL d := hmLval dS
          _ = a.1 := had.symm
      · apply Subtype.ext
        calc
          (mR dS).1 = sR d := hmRval dS
          _ = b.1 := hbd.symm
    · rintro ⟨d, rfl, rfl⟩
      apply Subtype.ext
      calc
        (jL (mL d)).1 = iL (mL d).1 := hjLval (mL d)
        _ = iL (sL d.1) := congrArg iL (hmLval d)
        _ = iR (sR d.1) :=
          (hfree.overlap (sL d.1) (sR d.1)).mpr
            ⟨d.1, rfl, rfl⟩
        _ = iR (mR d).1 := congrArg iR (hmRval d).symm
        _ = (jR (mR d)).1 := (hjRval (mR d)).symm
  · intro R z
    constructor
    · intro hz
      have hz0 : Whole.rel R (incW ∘ z) :=
        (incW.map_rel_iff R z).mpr hz
      rcases (hfree.rel_iff R (incW ∘ z)).mp hz0 with
        ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
      · have hxS : ∀ k, iL (x k) ∈ S := by
          intro k
          have hk := congrFun heq k
          have hzS := (z k).2
          change (incW (z k)).1 ∈ S at hzS
          rw [hk] at hzS
          exact hzS
        let xs : Fin (L.relArity R) → Lset :=
          fun k => ⟨x k, hxS k⟩
        have hrelLS : LS.rel R xs := hx
        refine Or.inl ⟨xs, hrelLS, ?_⟩
        funext k
        apply Subtype.ext
        calc
          (z k).1 = (incW (z k)).1 := rfl
          _ = iL (x k) := congrFun heq k
          _ = (jL (xs k)).1 := (hjLval (xs k)).symm
      · have hxS : ∀ k, iR (x k) ∈ S := by
          intro k
          have hk := congrFun heq k
          have hzS := (z k).2
          change (incW (z k)).1 ∈ S at hzS
          rw [hk] at hzS
          exact hzS
        let xs : Fin (L.relArity R) → Rset :=
          fun k => ⟨x k, hxS k⟩
        have hrelRS : RS.rel R xs := hx
        refine Or.inr ⟨xs, hrelRS, ?_⟩
        funext k
        apply Subtype.ext
        calc
          (z k).1 = (incW (z k)).1 := rfl
          _ = iR (x k) := congrFun heq k
          _ = (jR (xs k)).1 := (hjRval (xs k)).symm
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact (jL.map_rel_iff R x).mpr hx
      · exact (jR.map_rel_iff R x).mpr hx
  · intro F0 x y
    constructor
    · intro hy
      have hy0 : incW y ∈ Whole.func F0 (incW ∘ x) := by
        have himg :
            incW y ∈ imageSet incW (WS.func F0 x) :=
          ⟨y, hy, rfl⟩
        rw [incW.map_func F0 x] at himg
        exact himg
      rcases (hfree.func_iff F0 (incW ∘ x) (incW y)).mp hy0 with
        ⟨a, b, hb, hargs, hout⟩ |
        ⟨a, b, hb, hargs, hout⟩
      · have haS : ∀ k, iL (a k) ∈ S := by
          intro k
          have hk := congrFun hargs k
          have hxS := (x k).2
          change (incW (x k)).1 ∈ S at hxS
          rw [hk] at hxS
          exact hxS
        have hbS : iL b ∈ S := by
          have hyS := y.2
          change (incW y).1 ∈ S at hyS
          rw [hout] at hyS
          exact hyS
        let as : Fin (L.funcArity F0) → Lset :=
          fun k => ⟨a k, haS k⟩
        let bs : Lset := ⟨b, hbS⟩
        have hbLS : bs ∈ LS.func F0 as := hb
        refine Or.inl ⟨as, bs, hbLS, ?_, ?_⟩
        · funext k
          apply Subtype.ext
          calc
            (x k).1 = (incW (x k)).1 := rfl
            _ = iL (a k) := congrFun hargs k
            _ = (jL (as k)).1 := (hjLval (as k)).symm
        · apply Subtype.ext
          calc
            y.1 = (incW y).1 := rfl
            _ = iL b := hout
            _ = (jL bs).1 := (hjLval bs).symm
      · have haS : ∀ k, iR (a k) ∈ S := by
          intro k
          have hk := congrFun hargs k
          have hxS := (x k).2
          change (incW (x k)).1 ∈ S at hxS
          rw [hk] at hxS
          exact hxS
        have hbS : iR b ∈ S := by
          have hyS := y.2
          change (incW y).1 ∈ S at hyS
          rw [hout] at hyS
          exact hyS
        let as : Fin (L.funcArity F0) → Rset :=
          fun k => ⟨a k, haS k⟩
        let bs : Rset := ⟨b, hbS⟩
        have hbRS : bs ∈ RS.func F0 as := hb
        refine Or.inr ⟨as, bs, hbRS, ?_, ?_⟩
        · funext k
          apply Subtype.ext
          calc
            (x k).1 = (incW (x k)).1 := rfl
            _ = iR (a k) := congrFun hargs k
            _ = (jR (as k)).1 := (hjRval (as k)).symm
        · apply Subtype.ext
          calc
            y.1 = (incW y).1 := rfl
            _ = iR b := hout
            _ = (jR bs).1 := (hjRval bs).symm
    · rintro (⟨a, b, hb, hargs, hout⟩ |
        ⟨a, b, hb, hargs, hout⟩)
      · exact (jL.map_func F0 a) ▸
          ⟨b, hb, hout⟩
      · exact (jR.map_func F0 a) ▸
          ⟨b, hb, hout⟩

end StructuralRamsey.Structure.IsFreeAmalgam
