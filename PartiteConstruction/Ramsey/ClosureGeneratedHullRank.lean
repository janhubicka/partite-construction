import PartiteConstruction.Ramsey.ClosureUSize2019

/-! # The generating-rank bridge for the positive Theorem 2.18 proof

For a finite vertex set S in C, its ambient U-closure may have many more
vertices than S. What the local-completion argument needs is the valid
inequality USize(C induced on cl_U(S)) <= |S|, not equality of the
U-sizes of a weak test and its closure, and not a bound on hull cardinality.

The proof works with relative U-substructures and is independent of the
intrinsic/relative irreducibility choice. U-closedness of C is used only
when the resulting hull must also be intrinsically U-closed.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Relative U-closure is transitive through an induced U-substructure.
The image is the exact image of the indicated subset, not a new hull. -/
theorem IsUSubstructure.image_inclusion
    {rules : ClosureDescription L} {A : RelStructure L V}
    {T : Set V} (hT : IsUSubstructure rules A T)
    {R : Set T} (hR : IsUSubstructure rules (A.induce T) R) :
    IsUSubstructure rules A (Subtype.val '' R) := by
  intro rule hrule t ht hRoot j
  have hRootT : ∀ k : Fin rule.rootSize,
      t (k.castLE rule.rootLE) ∈ T := by
    intro k
    obtain ⟨x, _, hx⟩ := hRoot k
    rw [← hx]
    exact x.2
  have hAllT : ∀ k : Fin (L.arity rule.symbol), t k ∈ T :=
    hT rule hrule t ht hRootT
  let tT : Fin (L.arity rule.symbol) → T :=
    fun k => ⟨t k, hAllT k⟩
  have htT : (A.induce T).rel rule.symbol tT := ht
  have hRootR : ∀ k : Fin rule.rootSize,
      tT (k.castLE rule.rootLE) ∈ R := by
    intro k
    obtain ⟨x, hxR, hx⟩ := hRoot k
    have hxT : x = tT (k.castLE rule.rootLE) := Subtype.ext hx
    rw [← hxT]
    exact hxR
  exact ⟨tT j, hR rule hrule tT htT hRootR j, rfl⟩

/-- The original vertices generate the induced structure on their
ambient U-closure. No finiteness or intrinsic closedness is required. -/
theorem UClosureHull_induce_generated
    (rules : ClosureDescription L) (A : RelStructure L V)
    (S : Set V) :
    IsUGenerating rules (A.induce (UClosureHull rules A S))
      {x : UClosureHull rules A S | x.1 ∈ S} := by
  let T : Set V := UClosureHull rules A S
  let G : Set T := {x | x.1 ∈ S}
  let H : Set T := UClosureHull rules (A.induce T) G
  have hT : IsUSubstructure rules A T :=
    UClosureHull_isUSubstructure rules A S
  have hH : IsUSubstructure rules (A.induce T) H :=
    UClosureHull_isUSubstructure rules (A.induce T) G
  have hImage : IsUSubstructure rules A (Subtype.val '' H) :=
    hT.image_inclusion hH
  have hSImage : S ⊆ Subtype.val '' H := by
    intro x hx
    let y : T := ⟨x, subset_UClosureHull rules A S hx⟩
    have hyG : y ∈ G := hx
    exact ⟨y, subset_UClosureHull rules (A.induce T) G hyG, rfl⟩
  have hTImage : T ⊆ Subtype.val '' H :=
    UClosureHull_minimal rules A hImage hSImage
  change H = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hyH, hyx⟩ := hTImage x.2
  have heq : y = x := Subtype.ext hyx
  rw [← heq]
  exact hyH

/-- Any specified finite generating set bounds the minimum rank. -/
theorem USize_le_of_generating
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (S : Finset V) (hS : IsUGenerating rules A (↑S : Set V)) :
    USize rules A ≤ S.card := by
  classical
  exact Nat.find_min' (exists_UGenerating_card rules A) ⟨S, rfl, hS⟩

/-- The closure hull of a finite tested set has U-size at most the
number of tested vertices, regardless of the hull's vertex cardinality. -/
theorem USize_induce_UClosureHull_le
    (rules : ClosureDescription L) (A : RelStructure L V)
    (S : Finset V)
    [Fintype (UClosureHull rules A (↑S : Set V))] :
    USize rules (A.induce (UClosureHull rules A (↑S : Set V))) ≤ S.card := by
  classical
  let T : Set V := UClosureHull rules A (↑S : Set V)
  let inc : (↑S : Set V) ↪ T := {
    toFun := fun x => ⟨x.1, subset_UClosureHull rules A (↑S : Set V) x.2⟩
    inj' := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : T => z.1) h
  }
  let G : Finset T := S.attach.map inc
  have hG : (↑G : Set T) = {x : T | x.1 ∈ (↑S : Set V)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
      have hyx : y.1 = x.1 := congrArg (fun z : T => z.1) hy
      change x.1 ∈ S
      rw [← hyx]
      exact y.2
    · intro hx
      let y : (↑S : Set V) := ⟨x.1, hx⟩
      apply Finset.mem_map.mpr
      refine ⟨y, Finset.mem_attach S y, ?_⟩
      exact Subtype.ext rfl
  have hGen : IsUGenerating rules (A.induce T) (↑G : Set T) := by
    rw [hG]
    exact UClosureHull_induce_generated rules A (↑S : Set V)
  have hCard : G.card = S.card := by simp [G]
  calc
    USize rules (A.induce T) ≤ G.card :=
      USize_le_of_generating rules (A.induce T) G hGen
    _ = S.card := hCard

end StructuralRamsey.RelStructure
