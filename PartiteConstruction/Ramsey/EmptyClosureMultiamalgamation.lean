import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-! # The U=empty instance of the 2019 multiamalgamation theorem

For U=empty, every small substructure is U-closed, and the notions of
U-irreducible and U-homomorphism-embedding are the ordinary relational
ones. Theorem 2.18 of *All those Ramsey classes* then follows from:

1. the verified strict RELATIONAL sparsening theorem;
2. the just-proved K-completion of strict B-trees by strong amalgamation;
3. the locally finite completion axiom n(B,C0); and
4. the verified B-copywise colouring transfer.

This formalization uses exactly the tested vertex set, without
replacing weak small substructures by a generated closure.
The final K-completion map is required to preserve all B-copies,
not to be a global homomorphism.

The full Theorem 2.18 for an arbitrary nonempty closure description U
remains a separate goal.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- The exact local finiteness condition of Definition 2.17(4) when
U is empty, at fixed base B and fixed original Ramsey witness C0.
All small tested substructures are ordinary, vertex-exact relational
induced substructures. The final conclusion is only B-copywise. -/
def EmptyClosureLocalFiniteness
    (K : StructureClass.{u,v} (L := L))
    (Base : RelStructure L VB)
    (C₀ : RelStructure L P) : Prop :=
  ∃ n : ℕ,
    ∀ {W : Type v} [Finite W] (C : RelStructure L W),
      (∃ p : W → P, C.IsHomomorphismEmbedding C₀ p) →
      (∀ {X : Type v} [Finite X] (E : RelStructure L X),
        E.Irreducible → Embedding E C → K E) →
      (∀ S : Finset W, S.card ≤ n →
        HasKHomCompletion K (C.induce (↑S : Set W))) →
      HasCopywiseCompletion K Base C

/-- Main empty-closure multiamalgamation transfer at fixed A,B,C0.
The category K need not be freely amalgamating. All function issues
are absent here: U is empty, and the proof is a genuinely relational
special case of the published 2019 Theorem 2.18. -/
theorem ramsey_of_emptyClosure_multiamalgamation
    (K : StructureClass.{u,v} (L := L))
    (hK : FiniteStrongAmalgamationClass K)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C₀ : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : A.Irreducible)
    (hB : B.Irreducible)
    (hKB : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B C₀ κ)
    (hLoc : EmptyClosureLocalFiniteness K B C₀) :
    ∃ (X : Type v) (_ : Finite X) (C : RelStructure L X),
      K C ∧ StructuralRamsey.Arrow A B C κ := by
  classical
  obtain ⟨n,hn⟩ := hLoc
  obtain ⟨W,hW,C,hArrow,p,hProj,hLocal,hExt⟩ :=
    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all
      A B C₀ κ hRamsey hB n
  letI : Finite W := hW
  have hSmall :
      ∀ S : Finset W, S.card ≤ n →
        HasKHomCompletion K (C.induce (↑S : Set W)) := by
    intro S hSize
    exact (hLocal S hSize).toKCompletion hB hK hKB
  have hIrred :
      ∀ {Y : Type v} [Finite Y] (E : RelStructure L Y),
        E.Irreducible → Embedding E C → K E := by
    intro Y hY E hE e
    exact hExt.mem_irreducibles hK hKB E hE e
  have hC : HasCopywiseCompletion K B C :=
    hn C ⟨p,hProj⟩ hIrred hSmall
  exact arrow_of_copywiseCompletion_inClass hA hArrow hExt hC

end StructuralRamsey.RelStructure
