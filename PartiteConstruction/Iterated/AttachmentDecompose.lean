import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Relational.Attachment

/-! # Decomposing subsets of a free attachment

Fix one attached-copy index.  Any induced subset of the attachment is the free
amalgam of the part lying in that copy and the complementary rest, over their
common core.  This is the precise structural decomposition used in the mixed
case of the iterated partite construction.
-/
namespace StructuralRamsey.RelStructure.Attachment

noncomputable section

universe u v w z
variable {L : RelLanguage.{u}}
variable {V : Type v} {W : Type w} {I : Type z}
variable (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
variable (f : I → Embedding (B.induce S) D)

abbrev AV (S : Set V) (W : Type w) (I : Type z) :=
  Vertex S (W := W) (I := I)

def InCopy (i : I) (z : AV S W I) : Prop :=
  ∃ x : V, z = copyMap B S D f i x

def OutsideAt (i : I) (z : AV S W I) : Prop :=
  ∃ x : {x : V // x ∉ S}, z = .inr (i, x)

variable (T : Set (AV S W I)) (i : I)

def pieceSet : Set T := {z | InCopy B S D f i z.1}
def restSet : Set T := {z | ¬ OutsideAt (W := W) (I := I) S i z.1}
def overlapSet : Set T := {z | z ∈ pieceSet B S D f T i ∧ z ∈ restSet (W := W) (I := I) S T i}

abbrev Small := (attach B S D f).induce T
abbrev Piece := (Small B S D f T).induce (pieceSet B S D f T i)
abbrev Rest := (Small B S D f T).induce (restSet (W := W) (I := I) S T i)
abbrev Overlap := (Small B S D f T).induce (overlapSet (W := W) (I := I) B S D f T i)

abbrev PieceV := pieceSet B S D f T i
abbrev RestV := restSet (W := W) (I := I) S T i
abbrev OverlapV := overlapSet (W := W) (I := I) B S D f T i

def overlapToPiece :
    Embedding (Overlap B S D f T i) (Piece B S D f T i) where
  toFun x := ⟨x.1, x.2.1⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun q : PieceV B S D f T i => q.1) h
  map_rel_iff := fun _ _ => Iff.rfl

def overlapToRest :
    Embedding (Overlap B S D f T i) (Rest B S D f T i) where
  toFun x := ⟨x.1, x.2.2⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun q : RestV (W := W) (I := I) S T i => q.1) h
  map_rel_iff := fun _ _ => Iff.rfl

def pieceInclusion :
    Embedding (Piece B S D f T i) (Small B S D f T) :=
  inclusion (Small B S D f T) (pieceSet B S D f T i)

def restInclusion :
    Embedding (Rest B S D f T i) (Small B S D f T) :=
  inclusion (Small B S D f T) (restSet (W := W) (I := I) S T i)

theorem copyMap_not_outside_of_ne
    (j : I) (hji : j ≠ i) (x : V) :
    ¬ OutsideAt (W := W) (I := I) S i (copyMap B S D f j x) := by
  classical
  intro h
  rcases h with ⟨y, hy⟩
  by_cases hx : x ∈ S
  · rw [copyMap_mem j x hx] at hy
    simp at hy
  · rw [copyMap_not_mem j x hx] at hy
    have : j = i := by
      exact congrArg (fun z => z.1) (Sum.inr.inj hy)
    exact hji this

/-- The induced subset is exactly the free amalgam of the chosen copy piece
and the rest. -/
theorem decompose :
    IsFreeAmalgam
      (overlapToPiece B S D f T i)
      (overlapToRest B S D f T i)
      (pieceInclusion B S D f T i)
      (restInclusion B S D f T i) := by
  classical
  constructor
  · intro z
    by_cases hout : OutsideAt (W := W) (I := I) S i z.1
    · rcases hout with ⟨x, hx⟩
      let e : PieceV B S D f T i :=
        ⟨z, ⟨x.1, by
          rw [hx]
          symm
          exact copyMap_not_mem i x.1 x.2⟩⟩
      exact Or.inl ⟨e, rfl⟩
    · let r : RestV (W := W) (I := I) S T i := ⟨z, hout⟩
      exact Or.inr ⟨r, rfl⟩
  · intro e r
    constructor
    · intro her
      have hval : e.1 = r.1 := by
        change e.1 = r.1 at her
        exact her
      let z : T := e.1
      have hp : z ∈ pieceSet B S D f T i := e.2
      have hr : z ∈ restSet (W := W) (I := I) S T i := by
        change ¬ OutsideAt (W := W) (I := I) S i z.1
        intro hout
        apply r.2
        change OutsideAt (W := W) (I := I) S i r.1.1
        rw [← hval]
        exact hout
      let h : OverlapV (W := W) (I := I) B S D f T i := ⟨z, hp, hr⟩
      refine ⟨h, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hval.symm
    · rintro ⟨h, rfl, rfl⟩
      rfl
  · intro R z
    constructor
    · intro hz
      change (attach B S D f).rel R (Subtype.val ∘ z) at hz
      rcases hz with hcore | hcopy
      · rcases hcore with ⟨y, hy, heq⟩
        have hrest : ∀ k, (z k) ∈ restSet (W := W) (I := I) S T i := by
          intro k
          change ¬ OutsideAt (W := W) (I := I) S i (z k).1
          intro hout
          rcases hout with ⟨x, hx⟩
          have hk : (z k).1 = Sum.inl (y k) := by
            simpa [Function.comp_apply] using congrFun heq k
          rw [hx] at hk
          simp at hk
        let zr : Fin (L.arity R) → RestV (W := W) (I := I) S T i :=
          fun k => ⟨z k, hrest k⟩
        refine Or.inr ⟨zr, ?_, ?_⟩
        · change (attach B S D f).rel R
            (Subtype.val ∘ (Subtype.val ∘ zr))
          exact Or.inl ⟨y, hy, by
            funext k
            simpa [Function.comp_apply] using congrFun heq k⟩
        · funext k
          rfl
      · rcases hcopy with ⟨j, y, hy, heq⟩
        by_cases hji : j = i
        · subst j
          have hpiece : ∀ k, (z k) ∈ pieceSet B S D f T i := by
            intro k
            refine ⟨y k, ?_⟩
            exact congrFun heq k
          let ze : Fin (L.arity R) → PieceV B S D f T i :=
            fun k => ⟨z k, hpiece k⟩
          refine Or.inl ⟨ze, ?_, ?_⟩
          · change (attach B S D f).rel R
              (Subtype.val ∘ (Subtype.val ∘ ze))
            exact Or.inr ⟨i, y, hy, by
              funext k
              simpa [Function.comp_apply] using congrFun heq k⟩
          · funext k
            rfl
        · let zr : Fin (L.arity R) → RestV (W := W) (I := I) S T i :=
            fun k => ⟨z k, by
              change ¬ OutsideAt (W := W) (I := I) S i (z k).1
              intro hout
              apply copyMap_not_outside_of_ne
                (B := B) (S := S) (D := D) (f := f)
                (i := i) j hji (y k)
              have hk : (z k).1 = copyMap B S D f j (y k) := by
                simpa [Function.comp_apply] using congrFun heq k
              rw [← hk]
              exact hout⟩
          refine Or.inr ⟨zr, ?_, ?_⟩
          · change (attach B S D f).rel R
              (Subtype.val ∘ (Subtype.val ∘ zr))
            exact Or.inr ⟨j, y, hy, by
              funext k
              simpa [Function.comp_apply] using congrFun heq k⟩
          · funext k
            rfl
    · rintro (⟨ze, hze, heq⟩ | ⟨zr, hzr, heq⟩)
      · change (attach B S D f).rel R (Subtype.val ∘ z)
        change (attach B S D f).rel R
          (Subtype.val ∘ (Subtype.val ∘ ze)) at hze
        convert hze using 1
        funext k
        have hk := congrFun heq k
        exact congrArg Subtype.val hk
      · change (attach B S D f).rel R (Subtype.val ∘ z)
        change (attach B S D f).rel R
          (Subtype.val ∘ (Subtype.val ∘ zr)) at hzr
        convert hzr using 1
        funext k
        have hk := congrFun heq k
        exact congrArg Subtype.val hk

end

end StructuralRamsey.RelStructure.Attachment
