import PartiteConstruction.Relational.FreeAmalgamationClass
import PartiteConstruction.Iterated.SparseningStrictBaseIrreducible
import PartiteConstruction.Iterated.Ordered
import PartiteConstruction.Ramsey.Ordered

/-! # Evans--Hubicka--Nesetril Ramsey theorem for free-amalgamation classes

For a hereditary relational class closed under free amalgamation, adding a
linear order gives a Ramsey class.

The proof is assembled from the already verified constructions.  First use the
unrestricted ordered relational Ramsey theorem.  Then apply the strict
irreducible-base sparsening theorem once (with local depth one).  Its final
irreducible-extension property says that every irreducible substructure of the
sparse witness is contained in a copy of B.  The finite member test for
free-amalgamation classes therefore puts the order reduct back in the class.
Finally complete the partial order produced by the sparsening projection.

This formulation is intentionally independent of girth and is the reusable
entry point for lean-girth.
-/
namespace StructuralRamsey.RelStructure.FreeAmalgamationClass

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- EHN, in the slightly stronger fixed-target form: membership of the target
B suffices to construct a Ramsey witness in K. -/
theorem orderedRamsey_of_mem_target
    {K : RelStructure.StructureClass (L := L)}
    (hK : RelStructure.FreeAmalgamationClass K)
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hBmem : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      K C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ := by
  classical
  obtain ⟨P, hP, oP, C₀, hRamsey⟩ :=
    StructuralRamsey.Partite.orderedRamsey A B κ
  letI : Finite P := hP
  letI : LinearOrder P := oP
  have hBirr : B.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible B).irreducible
  obtain ⟨W, hW, Cplus, hArrow, p, hp, _hLocal, hExtend⟩ :=
    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all
      A.ordered B.ordered C₀.ordered κ hRamsey hBirr 1
  letI : Finite W := hW
  have hpart :
      ∀ x y, Cplus.rel (.inr ()) ![x, y] → p x < p y := by
    intro x y hxy
    have hmap := hp.1 (.inr ()) ![x, y] hxy
    have heq : p ∘ ![x, y] = ![p x, p y] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp
      (congrArg
        (C₀.ordered.rel (show L.withOrder.Symbol from .inr ())) heq)
      hmap
  obtain ⟨oW, horder⟩ :=
    RelStructure.exists_order_extension Cplus p hpart
  letI : LinearOrder W := oW
  let C : RelStructure L W := Cplus.orderReduct
  have hCmem : K C := by
    apply hK.mem_of_irreducibles
    intro X _ E hE e
    let S : Set W := Set.range e
    have hSred : (C.induce S).Irreducible :=
      hE.range_embedding e
    have hSplus : (Cplus.induce S).Irreducible := by
      intro x y hxy
      obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hSred hxy
      refine ⟨(.inl R : L.withOrder.Symbol), z, i, j, ?_, hzi, hzj⟩
      exact hz
    obtain ⟨β, hβ⟩ := hExtend S hSplus
    let βr : RelStructure.Embedding B C := {
      toFun := β
      injective := β.injective
      map_rel_iff := by
        intro R z
        exact β.map_rel_iff (.inl R) z
    }
    have hrange : ∀ x : X, ∃ b : V, e x = βr b := by
      intro x
      let z : S := ⟨e x, ⟨x, rfl⟩⟩
      obtain ⟨b, hb⟩ := hβ z
      exact ⟨b, hb⟩
    let eB : RelStructure.Embedding E B :=
      e.factorThroughRange βr hrange
    exact hK.hereditary hBmem eB
  have hArrowFinal :
      StructuralRamsey.Arrow A.ordered B.ordered C.ordered κ := by
    simpa [C, RelStructure.completeOrder] using
      (RelStructure.arrow_completeOrder A B Cplus horder κ hArrow)
  exact ⟨W, hW, oW, C, hCmem, hArrowFinal⟩

/-- Standard Ramsey-class formulation of EHN.  The source membership
hypothesis is part of the class statement; the construction itself only needs
the target membership. -/
theorem orderedRamsey
    {K : RelStructure.StructureClass (L := L)}
    (hK : RelStructure.FreeAmalgamationClass K)
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (_hAmem : K A) (hBmem : K B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      K C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ :=
  orderedRamsey_of_mem_target hK A B hBmem κ

end StructuralRamsey.RelStructure.FreeAmalgamationClass
