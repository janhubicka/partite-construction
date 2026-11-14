import PartiteConstruction.Structure.GenericUOriginalPictureProperty
import PartiteConstruction.Structure.GenericUWitnessTransversality
import PartiteConstruction.Structure.GenericUGraphProjection
import PartiteConstruction.Structure.GenericUGraphProjectionInverse
import PartiteConstruction.Structure.GenericUOrdinaryClosedEmbedding
import PartiteConstruction.Functional.ClosedPicture

/-!
# Track F — the actual arbitrary-(L,U) Induced Picture Lemma with closures

This is the original relational-language version of the survey's
lem:indpicutreU, with genuine same-carrier D-partite witnesses, U-output
transversality, original U-closed A-copies with prescribed projection α,
and the full monochromatic closed B-copy property.

The proof applies the previously verified graph-language Picture Lemma
and decodes its arbitrary witness. It is NOT a consequence of the final
ordered Ramsey theorem, and does not introduce a coherence assumption.
-/

namespace StructuralRamsey.Partite.OriginalUClosed

universe u v
variable {L : RelLanguage.{u}} {P T V : Type v}

/-- The original-relational target D is exactly its decoded nonredundant
U-function graph. Every symbol and tuple retains its truth value. -/
theorem from_asReducedUGraph_eq
    (D : RelStructure L P)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 1 ≤ L.arity R) :
    RelStructure.fromReducedUGraph U hU
      (D.asReducedUGraph U hU) = D := by
  apply RelStructure.mk.injEq.mpr
  funext R t
  exact propext (D.from_asReducedUGraph_rel_iff U hU R t)

/-- Literal closed original induced Picture lemma, for arbitrary relation
language L and designated U-relations of arity >= 2, including nullary
non-U relations, empty U-fibres and repeated tuple entries. -/
theorem pictureLemma
    (A : RelStructure L T)
    (D : RelStructure L P)
    (B : Partite.System L P V)
    (U : Set L.Symbol)
    (hU : ∀ R, R ∈ U → 2 ≤ L.arity R)
    (α : {f : RelStructure.Embedding A D //
      RelStructure.IsUClosedEmbeddingRange U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) f})
    (hB : B.IsPartiteOver D)
    (hT : B.OriginalUOutputTransversal U
      (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)))
    [Finite T] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ (X : Type v) (_ : Finite X) (C : Partite.System L P X),
      C.IsPartiteOver D ∧
      C.OriginalUOutputTransversal U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)) ∧
      PictureProperty A B (fun x => α.1 x) C U
        (fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR))
        κ := by
  classical
  let hU1 : ∀ R, R ∈ U → 1 ≤ L.arity R :=
    fun R hR => Nat.le_trans (by decide : 1 ≤ 2) (hU R hR)
  let A_g := A.asReducedUGraph U hU1
  let D_g := D.asReducedUGraph U hU1
  let B_g := B.asReducedUGraph U hU1
  let α_g : RelStructure.ClosedEmbedding A_g D_g :=
    (RelStructure.Embedding.uClosedReducedGraphEquiv
      (A := A) (B := D) U hU1) α
  have hPartG : B_g.IsPartiteOver D_g :=
    Partite.System.isPartiteOver_asReducedUGraph D B U hU1 hB
  have hTG : B_g.FunctionOutputTransversal :=
    (B.originalUOutputTransversal_iff U hU1).mp hT
  obtain ⟨X, hX, C_g, hCPartG, hCTG, hPicG⟩ :=
    Partite.Closed.Picture.pictureLemma
      (A := A_g) (D := D_g) (B := B_g) (α := α_g)
      hPartG hTG κ
  let C := Partite.System.fromReducedUGraph U hU1 C_g
  have hPart : C.IsPartiteOver D := by
    have hPartDecoded :
        C.IsPartiteOver (RelStructure.fromReducedUGraph U hU1 D_g) :=
      Partite.System.isPartiteOver_fromReducedUGraph
        U hU1 D_g C_g hCPartG
    rw [from_asReducedUGraph_eq D U hU1] at hPartDecoded
    exact hPartDecoded
  have hTrans : C.OriginalUOutputTransversal U hU1 :=
    (Partite.System.originalUOutputTransversal_decode_iff
      U hU1 C_g).mpr hCTG
  have hP : PictureProperty A B (fun x => α.1 x) C U hU1 κ := by
    exact pictureProperty_of_graph A B (fun x => α.1 x) U hU1
      C_g κ (by simpa only [A_g, B_g] using hPicG)
  exact ⟨X, hX, C, hPart, hTrans, hP⟩

end StructuralRamsey.Partite.OriginalUClosed
