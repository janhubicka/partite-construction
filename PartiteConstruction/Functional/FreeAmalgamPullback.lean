import PartiteConstruction.Functional.MixedOverlapExactness

/-! # Pulling an embedded substructure through a functional free amalgam

A full embedding into a functional free amalgam pulls the two closed side
ranges back to closed subsets of its domain.  These subsets form a free
amalgam decomposition of the domain.  We additionally retain the factor
embeddings into the two ambient sides and a common factor through the ambient
overlap.  This is the diagram needed to transport projected partial
A-intersections through a mixed functional Picture step.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {H E F C U : Type v}
variable {Dsrc : Structure L H} {Esrc : Structure L E}
variable {Fsrc : Structure L F} {Csrc : Structure L C}
variable {A : Structure L U}
variable {sE : Embedding Dsrc Esrc} {sF : Embedding Dsrc Fsrc}
variable {iE : Embedding Esrc Csrc} {iF : Embedding Fsrc Csrc}

/-- Pullback of a full free-amalgam diagram along a full embedding. -/
structure EmbeddingPullback
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding A Csrc) where
  Common : Type v
  Left : Type v
  Right : Type v
  common : Structure L Common
  left : Structure L Left
  right : Structure L Right
  toLeft : Embedding common left
  toRight : Embedding common right
  leftIn : Embedding left A
  rightIn : Embedding right A
  free : IsFreeAmalgam toLeft toRight leftIn rightIn
  leftMap : Embedding left Esrc
  rightMap : Embedding right Fsrc
  commonMap : Embedding common Dsrc
  left_factor : ∀ x, e (leftIn x) = iE (leftMap x)
  right_factor : ∀ x, e (rightIn x) = iF (rightMap x)
  common_left : ∀ x, leftMap (toLeft x) = sE (commonMap x)
  common_right : ∀ x, rightMap (toRight x) = sF (commonMap x)
  left_reflect : ∀ a d, leftMap a = sE d →
    ∃ z, a = toLeft z ∧ commonMap z = d
  right_reflect : ∀ b d, rightMap b = sF d →
    ∃ z, b = toRight z ∧ commonMap z = d

/-- Every full embedding into a functional free amalgam has the canonical
closed pullback diagram. -/
noncomputable def embeddingPullback
    (hfree : IsFreeAmalgam sE sF iE iF)
    (e : Embedding A Csrc) :
    EmbeddingPullback hfree e := by
  classical
  let LE : Set C := Set.range iE
  let RF : Set C := Set.range iF
  have hLE : Csrc.IsClosed LE := iE.range_isClosed
  have hRF : Csrc.IsClosed RF := iF.range_isClosed
  let Lset : Set U := {a | e a ∈ LE}
  let Rset : Set U := {a | e a ∈ RF}
  have hLclosed : A.IsClosed Lset := e.preimage_isClosed LE hLE
  have hRclosed : A.IsClosed Rset := e.preimage_isClosed RF hRF
  let Mset : Set U := Lset ∩ Rset
  have hMclosed : A.IsClosed Mset := by
    intro F0 x hx y hy
    exact ⟨
      hLclosed F0 x (fun i => (hx i).1) hy,
      hRclosed F0 x (fun i => (hx i).2) hy⟩
  let AL := A.induce Lset hLclosed
  let AR := A.induce Rset hRclosed
  let AM := A.induce Mset hMclosed
  let mL : Embedding AM AL := {
    toFun := fun x => ⟨x.1, x.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Lset => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F0 x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyr : y.1 ∈ Rset :=
          hRclosed F0 (Subtype.val ∘ x)
            (fun i => (x i).2.2) hy
        exact ⟨⟨y.1, ⟨y.2, hyr⟩⟩, hy, rfl⟩
  }
  let mR : Embedding AM AR := {
    toFun := fun x => ⟨x.1, x.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Rset => z.1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F0 x
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        have hyl : y.1 ∈ Lset :=
          hLclosed F0 (Subtype.val ∘ x)
            (fun i => (x i).2.1) hy
        exact ⟨⟨y.1, ⟨hyl, y.2⟩⟩, hy, rfl⟩
  }
  let iL : Embedding AL A := inclusion A Lset hLclosed
  let iR : Embedding AR A := inclusion A Rset hRclosed
  have hInternal : IsFreeAmalgam mL mR iL iR := by
    constructor
    · intro a
      rcases hfree.covers (e a) with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact Or.inl ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨a, ⟨x, hx.symm⟩⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have huv : a.1 = b.1 := hab
        let z : Mset := ⟨a.1, ⟨a.2, by simpa [huv] using b.2⟩⟩
        refine ⟨z, rfl, ?_⟩
        apply Subtype.ext
        exact huv.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R z
      constructor
      · intro hz
        have hez : Csrc.rel R (e ∘ z) :=
          (e.map_rel_iff R z).mpr hz
        rcases (hfree.rel_iff R (e ∘ z)).mp hez with
          ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩
        · have hmem : ∀ k, z k ∈ Lset := by
            intro k
            exact ⟨x k, (congrFun heq k).symm⟩
          let zl : Fin (L.relArity R) → Lset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inl ⟨zl, hz, rfl⟩
        · have hmem : ∀ k, z k ∈ Rset := by
            intro k
            exact ⟨x k, (congrFun heq k).symm⟩
          let zr : Fin (L.relArity R) → Rset :=
            fun k => ⟨z k, hmem k⟩
          exact Or.inr ⟨zr, hz, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
    · intro F0 x y
      constructor
      · intro hy
        have hey : e y ∈ Csrc.func F0 (e ∘ x) := by
          have h : e y ∈ imageSet e (A.func F0 x) := ⟨y, hy, rfl⟩
          rw [e.map_func F0 x] at h
          exact h
        rcases (hfree.func_iff F0 (e ∘ x) (e y)).mp hey with
          ⟨a, b, hb, hargs, hout⟩ |
          ⟨a, b, hb, hargs, hout⟩
        · have hxL : ∀ k, x k ∈ Lset := by
            intro k
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyL : y ∈ Lset := ⟨b, hout.symm⟩
          let xl : Fin (L.funcArity F0) → Lset :=
            fun k => ⟨x k, hxL k⟩
          exact Or.inl ⟨xl, ⟨y, hyL⟩, hy, rfl, rfl⟩
        · have hxR : ∀ k, x k ∈ Rset := by
            intro k
            exact ⟨a k, (congrFun hargs k).symm⟩
          have hyR : y ∈ Rset := ⟨b, hout.symm⟩
          let xr : Fin (L.funcArity F0) → Rset :=
            fun k => ⟨x k, hxR k⟩
          exact Or.inr ⟨xr, ⟨y, hyR⟩, hy, rfl, rfl⟩
      · rintro (⟨a, b, hb, hargs, hout⟩ |
          ⟨a, b, hb, hargs, hout⟩)
        · subst x
          subst y
          exact hb
        · subst x
          subst y
          exact hb
  let eLeftC : Embedding AL Csrc := e.comp iL
  have hLeftRange : ∀ x : Lset, ∃ y : E, eLeftC x = iE y := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  let mapLeft : Embedding AL Esrc :=
    eLeftC.factorThroughRange iE hLeftRange
  have hLeftFactor (x : Lset) :
      e (iL x) = iE (mapLeft x) := by
    exact Classical.choose_spec (hLeftRange x)
  let eRightC : Embedding AR Csrc := e.comp iR
  have hRightRange : ∀ x : Rset, ∃ y : F, eRightC x = iF y := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  let mapRight : Embedding AR Fsrc :=
    eRightC.factorThroughRange iF hRightRange
  have hRightFactor (x : Rset) :
      e (iR x) = iF (mapRight x) := by
    exact Classical.choose_spec (hRightRange x)
  let leftCommon : Embedding AM Esrc := mapLeft.comp mL
  have hCommonRange :
      ∀ z : Mset, ∃ d : H, leftCommon z = sE d := by
    intro z
    have hcross :
        iE (mapLeft (mL z)) = iF (mapRight (mR z)) := by
      calc
        iE (mapLeft (mL z)) = e (iL (mL z)) :=
          (hLeftFactor (mL z)).symm
        _ = e (iR (mR z)) := by rfl
        _ = iF (mapRight (mR z)) :=
          hRightFactor (mR z)
    obtain ⟨d, hdE, _hdF⟩ :=
      (hfree.overlap (mapLeft (mL z)) (mapRight (mR z))).mp hcross
    exact ⟨d, hdE⟩
  let mapCommon : Embedding AM Dsrc :=
    leftCommon.factorThroughRange sE hCommonRange
  have hCommonLeft (z : Mset) :
      mapLeft (mL z) = sE (mapCommon z) := by
    exact Classical.choose_spec (hCommonRange z)
  have hCommonRight (z : Mset) :
      mapRight (mR z) = sF (mapCommon z) := by
    apply iF.injective
    calc
      iF (mapRight (mR z)) = iE (mapLeft (mL z)) := by
        symm
        calc
          iE (mapLeft (mL z)) = e (iL (mL z)) :=
            (hLeftFactor (mL z)).symm
          _ = e (iR (mR z)) := by rfl
          _ = iF (mapRight (mR z)) :=
            hRightFactor (mR z)
      _ = iE (sE (mapCommon z)) :=
        congrArg iE (hCommonLeft z)
      _ = iF (sF (mapCommon z)) :=
        (hfree.overlap (sE (mapCommon z)) (sF (mapCommon z))).mpr
          ⟨mapCommon z, rfl, rfl⟩
  have hLeftReflect :
      ∀ a d, mapLeft a = sE d →
        ∃ z : Mset, a = mL z ∧ mapCommon z = d := by
    intro a d had
    have hRightMem : a.1 ∈ Rset := by
      change e a.1 ∈ Set.range iF
      refine ⟨sF d, ?_⟩
      calc
        iF (sF d) = iE (sE d) :=
          ((hfree.overlap (sE d) (sF d)).mpr
            ⟨d, rfl, rfl⟩).symm
        _ = iE (mapLeft a) := congrArg iE had.symm
        _ = e (iL a) := hLeftFactor a
        _ = e a.1 := rfl
    let z : Mset := ⟨a.1, ⟨a.2, hRightMem⟩⟩
    have haz : a = mL z := by
      apply Subtype.ext
      rfl
    refine ⟨z, haz, ?_⟩
    apply sE.injective
    calc
      sE (mapCommon z) = mapLeft (mL z) :=
        (hCommonLeft z).symm
      _ = mapLeft a := congrArg mapLeft haz.symm
      _ = sE d := had
  have hRightReflect :
      ∀ b d, mapRight b = sF d →
        ∃ z : Mset, b = mR z ∧ mapCommon z = d := by
    intro b d hbd
    have hLeftMem : b.1 ∈ Lset := by
      change e b.1 ∈ Set.range iE
      refine ⟨sE d, ?_⟩
      calc
        iE (sE d) = iF (sF d) :=
          (hfree.overlap (sE d) (sF d)).mpr
            ⟨d, rfl, rfl⟩
        _ = iF (mapRight b) := congrArg iF hbd.symm
        _ = e (iR b) := hRightFactor b
        _ = e b.1 := rfl
    let z : Mset := ⟨b.1, ⟨hLeftMem, b.2⟩⟩
    have hbz : b = mR z := by
      apply Subtype.ext
      rfl
    refine ⟨z, hbz, ?_⟩
    apply sF.injective
    calc
      sF (mapCommon z) = mapRight (mR z) :=
        (hCommonRight z).symm
      _ = mapRight b := congrArg mapRight hbz.symm
      _ = sF d := hbd
  exact {
    Common := Mset
    Left := Lset
    Right := Rset
    common := AM
    left := AL
    right := AR
    toLeft := mL
    toRight := mR
    leftIn := iL
    rightIn := iR
    free := hInternal
    leftMap := mapLeft
    rightMap := mapRight
    commonMap := mapCommon
    left_factor := hLeftFactor
    right_factor := hRightFactor
    common_left := hCommonLeft
    common_right := hCommonRight
    left_reflect := hLeftReflect
    right_reflect := hRightReflect
  }

end StructuralRamsey.Structure.IsFreeAmalgam
