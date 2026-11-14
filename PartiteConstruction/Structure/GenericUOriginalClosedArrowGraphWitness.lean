import PartiteConstruction.Structure.GenericUOrdinaryClosedEmbedding
import PartiteConstruction.Structure.GenericUGraphWitnessRoundtripClosed
import PartiteConstruction.Structure.GenericUOriginalOrderedArrow
import PartiteConstruction.Functional.Closed

/-!
# Track F — exact original U-closed arrow for an arbitrary graph witness

A graph Ramsey construction returns an arbitrary graph-language target Cg,
not necessarily a canonical graph encoding of any previously fixed original
L-structure. The nonredundant U-graph language has an actual inverse
reindexing on the identical carrier. The verified two closed identity maps
allow transporting ALL colourings and closed embeddings from that
arbitrary graph target to the literal original decoded target.

No coherence, irreducibility, singleton-value or finite-language premise.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {T V P W : Type v}

/-- Exact equivalence of original U-closed A-copies in the decoded
ARBITRARY graph witness and graph-closed A-copies in that witness.
Underlying vertex injections are literally equal. -/
noncomputable def uClosedGraphWitnessEquiv
    (A : RelStructure L T)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C_g : Partite.System (L.withUFunctionsReduced U).graph P W) :
    {e : Embedding A
      (Partite.System.fromReducedUGraph U hU C_g).toRelStructure //
        IsUClosedEmbeddingRange U hU e} ≃
      ClosedEmbedding (A.asReducedUGraph U hU) C_g.toRelStructure := by
  classical
  let C := Partite.System.fromReducedUGraph U hU C_g
  let E := Embedding.uClosedReducedGraphEquiv
    (A := A) (B := C.toRelStructure) U hU
  let F := (Partite.System.graphRoundtripClosedForward U hU C_g).toRelClosed
  let G := (Partite.System.graphRoundtripClosedBackward U hU C_g).toRelClosed
  exact {
    toFun := fun e => ClosedEmbedding.comp F (E e)
    invFun := fun e => E.symm (ClosedEmbedding.comp G e)
    left_inv := by
      intro e
      apply Subtype.ext
      apply Embedding.ext
      intro x
      rfl
    right_inv := by
      intro e
      apply ClosedEmbedding.ext
      intro x
      rfl
  }

/-- Exact original U-closed Ramsey arrow decoded from a closed graph
Ramsey arrow on any partite witness, transporting every actual composition
of closed induced embeddings (rather than only a statement about colours). -/
theorem originalUClosedArrow_of_graphWitness
    (A : RelStructure L T)
    (B : RelStructure L V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R)
    (C_g : Partite.System (L.withUFunctionsReduced U).graph P W)
    (κ : Type*)
    (hG : ClosedArrow
      (A.asReducedUGraph U hU)
      (B.asReducedUGraph U hU) C_g.toRelStructure κ) :
    OriginalUClosedArrow A B
      (Partite.System.fromReducedUGraph U hU C_g).toRelStructure
      U hU κ := by
  classical
  let EA := uClosedGraphWitnessEquiv A U hU C_g
  let EB := uClosedGraphWitnessEquiv B U hU C_g
  let EAB := Embedding.uClosedReducedGraphEquiv
    (A := A) (B := B) U hU
  intro χ
  let χ_g : ClosedEmbedding
      (A.asReducedUGraph U hU) C_g.toRelStructure → κ :=
    fun e => χ (EA.symm e)
  obtain ⟨f_g, hf_g⟩ := hG χ_g
  refine ⟨EB.symm f_g, ?_⟩
  intro e₁ e₂
  have hcomp (e : {g : Embedding A B // IsUClosedEmbeddingRange U hU g}) :
      EA.symm (f_g.comp (EAB e)) =
        uClosedRangeComp U hU (EB.symm f_g) e := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  have hm := hf_g (EAB e₁) (EAB e₂)
  change χ (EA.symm (f_g.comp (EAB e₁))) =
    χ (EA.symm (f_g.comp (EAB e₂))) at hm
  rw [hcomp e₁, hcomp e₂] at hm
  exact hm

end StructuralRamsey.RelStructure
